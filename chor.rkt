#lang racket

(require math)
(require racket/set)
(require racket/date)
(require redex)

;; * Abbreviations
;;
;; - "chor" -- choreography
;; - "proc" -- process
;; - "net" -- network
;; - "cstore" -- choreographic store
;; - "pstore" -- process store
;; - "conf" -- configuration
;; - "defs" -- set of definitions (procedures)
;; - "def" -- definition (procedure)
;; - "wf" -- well-formed
;; - "pn" -- process names
;;
;; - "smc" -- Simple Choreographies
;; - "stc" -- Stateful Choreographies
;; - "coc" -- Conditional Choreographies
;; - "slc" -- Selective Choreographies
;; - "rcc" -- Recursive Choreographies
;;
;; - "smp" -- Simple Processes
;; - "stp" -- Stateful Processes
;; - "cop" -- Conditional Processes
;; - "slp" -- Selective Processes
;; - "rcp" -- Recursive Processes
;;
;; - suffix "p" -- process
;; - suffix "i" -- instruction
;; - suffix "c" -- choreography
;; - suffix "d" -- definition
;; - suffix "f" -- configuration

;; * TODO
;;
;; - Proper tests. Small examples are in the comments below.
;;
;; - Chapter 10.
;;
;; - Well-formedness for the runtime term.
;;
;; - Document the necessary safe-eval. Use the file transfer choreography as an
;;   example.
;;
;; - Add `r` as another role non-terminal to the chor languages to simplify
;;   things.
;;
;; - Document sorting behavior. E.g. "join" assumes that the networks are sorted
;;   when joining them together.
;;
;; - Document representation of choreographies, processes and stores -- they're
;;   just tagged (a)lists.
;;
;; - Document that we don't allow symbols or lists as values in expressions.

;;; * Util

;;; ** General

(define (aput k v alist #:equal? [equal? equal?] #:less? [less? <])
  (define (rec k v alist res)
    (match alist
      ['()
       (reverse (cons (cons k v) res))]
      [`(,(and c `(,k0 . ,_)) . ,tail)
       (cond
         [(equal? k k0)
          (append (reverse res) (cons (cons k v) tail))]
         [(less? k k0)
          (append (reverse res) (list* (cons k v) c tail))]
         [else
          (rec k v tail (cons c res))])]))
  (rec k v alist '()))

(define (set-disjoint? s1 s2)
  (empty? (set-intersect s1 s2)))

(define (applify proc)
  (lambda (args)
    (apply proc args)))

(define (partial proc . fixed)
  (lambda args (apply proc (append fixed args))))

;;; ** Common Language

(define-language Util
  (id ::= variable-not-otherwise-mentioned)
  ;; Expressions
  (v ::= any)
  (x f ::= id)
  (e ::= v x (f e ...))
  ;; Simple
  (p q r ::= id)
  (I ::= any)
  (C ::= (chor I ...))
  (P Q R ::= (proc I ...))
  (N M ::= (net (p P) ...))
  ;; Stateful
  (σ ::= (pstore (x v) ...))
  (Σ ::= (cstore (p σ) ...))
  ;; Selective
  (l ::= id)
  ;; Recursive
  (X ::= id)
  (CP ::= C P)
  (D ::= (defs (X ((p ...) CP)) ...)))

;;; ** Process Names

(define-metafunction Util
  pn : any -> (any ...)
  ;; Simple
  [(pn (p → q)) (p q)]
  ;; Stateful
  [(pn (p e → q x)) (p q)]
  [(pn (p x := e)) (p)]
  [(pn (p v → q)) (p q)]
  [(pn (τ @ p)) (p)]
  ;; Conditional
  [(pn (if (p e) C_1 C_2))
   ,(apply set-union (term ((p) (pn C_1) (pn C_2))))]
  ;; Selective
  [(pn (p → q [l])) (p q)]
  ;; Recursive
  [(pn (X p ...)) (p ...)]
  [(pn (enter (q ...) _ _)) (q ...)]
  ;; A whole choreography
  [(pn (chor I ...)) ((pn I) ...)])

;;; ** Transition Formatting

(define-metafunction Util
  format-μ : any -> string
  ;; Simple
  [(format-μ (p → q)) ,(apply format "~a → ~a" (term (p q)))]
  ;; Stateful
  [(format-μ (p v → q)) ,(apply format "~a.~s → ~a" (term (p v q)))]
  [(format-μ (τ @ p)) ,(apply format "τ@~a" (term (p)))]
  ;; Selective
  [(format-μ (p → q [l])) ,(apply format "~a → ~a [~a]" (term (p q l)))])

;;; ** Stores

(define (assoc-store k store [default (void)])
  (match store
    [`(,(or 'cstore 'pstore 'defs 'net) . ,alist)
     (let ([v (assoc k alist)])
       (if v (second v) default))]))

(define (put-store k v store)
  (match store
    [`(,(and store (or 'cstore 'pstore 'defs 'net)) . ,alist)
     `(,store ,@(aput k (list v) alist #:less? symbol<?))]))

(define-metafunction Util
  put-proc : N (p P) ... -> N
  [(put-proc N) N]
  [(put-proc N (p P) (q Q) ...)
   (put-proc ,(apply put-store (term (p P N))) (q Q) ...)])

(define-metafunction Util
  make-net : (p P) ... -> N
  [(make-net (p P) ...) (put-proc (net) (p P) ...)])

(define-metafunction Util
  get-pstore : Σ p -> σ
  [(get-pstore Σ p) ,(apply assoc-store (term (p Σ (pstore))))])

(define-metafunction Util
  get-var : σ x -> (boolean v)
  [(get-var σ x)
   (#t v)
   (where v ,(apply assoc-store (term (x σ))))
   (side-condition (not (equal? (term v) (void))))]
  [(get-var _ _) (#f 42)])

(define-metafunction Util
  put-var* : Σ p (x v) ... -> Σ
  [(put-var* Σ _) Σ]
  [(put-var* Σ p (x v) (x_1 v_1) ...)
   (put-var* ,(apply put-store (term (p σ Σ))) p (x_1 v_1) ...)
   (where σ_1 (get-pstore Σ p))
   (where σ ,(apply put-store (term (x v σ_1))))])

(define-metafunction Util
  put-var : Σ (p (x v) ...) ... -> Σ
  [(put-var Σ) Σ]
  [(put-var Σ (p (x v) ...) (p_1 (x_1 v_1) ...) ...)
   (put-var (put-var* Σ p (x v) ...) (p_1 (x_1 v_1) ...) ...)])

(define-metafunction Util
  make-cstore : (p (x v) ...) ... -> Σ
  [(make-cstore (p (x v) ...) ...) (put-var (cstore) (p (x v) ...) ...)])

(define-metafunction Util
  get-def : D X -> ((p ...) CP)
  [(get-def D X) ,(apply assoc-store (term (X D)))])

(define-metafunction Util
  put-def : D ((X p ...) CP) ... -> D
  [(put-def D) D]
  [(put-def D ((X p ...) CP) ((X_1 p_1 ...) CP_1) ...)
   (put-def ,(apply put-store (term (X ((p ...) CP) D)))
            ((X_1 p_1 ...) CP_1) ...)])

(define-metafunction Util
  make-defs : ((X p ...) CP) ... -> D
  [(make-defs ((X p ...) CP) ...) (put-def (defs) ((X p ...) CP) ...)])

;;; ** Evaluation

(define (eval-safe f args)
  (with-handlers ([exn:fail? (lambda (v)
                               ((error-display-handler) (exn-message v) v)
                               (list #f 42))])
    (list #t (apply (eval f) args))))

(define-judgment-form Util
  #:mode (↓ I I O)
  #:contract (↓ σ e v)
  [(side-condition ,(not (or (symbol? (term v)) (list? (term v)))))
   ---------------------------------------------------------------- val
   (↓ _ v v)]
  [(where (#t v) (get-var σ x))
   ---------------------------- var
   (↓ σ x v)]
  [(↓ σ e v)
   ...
   (where (#t v_1) ,(apply eval-safe (term (f (v ...)))))
   ------------------------------------------------------ call
   (↓ σ (f e ...) v_1)])

;; (judgment-holds (↓ (pstore (a 2) (b 3)) (+ 2 5 a b) v) v)
;; (show-derivations (build-derivations (↓ (pstore (a 2) (b 3)) (+ 2 5 a b) v)))

;; NOTE: If a process doesn't yet possess a referenced variable, the judgment
;; should just not hold, instead of throwing an error.
;;
;; (judgment-holds (↓ (pstore) x v) v)

;;; ** Substitution

(define-metafunction Util
  subst-p : p (p p) ... -> p
  [(subst-p p (p_1 q_1) ... (p q) (p_2 q_2) ...) q]
  [(subst-p p _ ...) p])

(define-metafunction Util
  subst : I (p p) ... -> I
  ;; Stateful
  [(subst (p e → q x) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) e → (subst-p q (p_1 q_1) ...) x)]
  [(subst (p x := e) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) x := e)]
  [(subst (p ! e) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) ! e)]
  [(subst (p ? x) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) ? x)]
  [(subst (x := e) _ ...)
   (x := e)]
  ;; Conditional
  [(subst (if (p e) (chor I_1 ...) (chor I_2 ...)) (p_1 q_1) ...)
   (if ((subst-p p (p_1 q_1) ...) e)
       (chor (subst I_1 (p_1 q_1) ...) ...)
       (chor (subst I_2 (p_1 q_1) ...) ...))]
  [(subst (if e (proc I_1 ...) (proc I_2 ...)) (p_1 q_1) ...)
   (if e
       (proc (subst I_1 (p_1 q_1) ...) ...)
       (proc (subst I_2 (p_1 q_1) ...) ...))]
  ;; Selective
  [(subst (p → q [l]) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) → (subst-p q (p_1 q_1) ...) [l])]
  [(subst (p ⊕ l) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) ⊕ l)]
  [(subst (p & (l (proc I ...)) ...) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) & (l (proc (subst I (p_1 q_1)) ...)) ...)]
  ;; Recursive
  [(subst (X p ...) (p_1 q_1) ...)
   (X (subst-p p (p_1 q_1) ...) ...)]
  [(subst (X p ...) (p_1 q_1) ...)
   (X (subst-p p (p_1 q_1) ...) ...)])

;;; ** Parallel Composition Commutativity

(define-judgment-form Util
  #:mode (commute I O)
  #:contract (commute N N)
  [--------------------------------------------- id
   (commute (net (p P) (q Q)) (net (p P) (q Q)))]
  [--------------------------------------------- commute
   (commute (net (p P) (q Q)) (net (q Q) (p P)))])

;;; ** Parallel Composition Associativity

(define-judgment-form Util
  #:mode (split I O O)
  #:contract (split N M M)
  [------------------------------------- done-left
   (split (net (p P)) (net (p P)) (net))]
  [------------------------------------- done-right
   (split (net (p P)) (net) (net (p P)))]
  [(split (net (q Q) ...) (net (r_1 R_1) ...) (net (r_2 R_2) ...))
   --------------------------------------------------------------------------- left
   (split (net (p P) (q Q) ...) (net (p P) (r_1 R_1) ...) (net (r_2 R_2) ...))]
  [(split (net (q Q) ...) (net (r_1 R_1) ...) (net (r_2 R_2) ...))
   --------------------------------------------------------------------------- right
   (split (net (p P) (q Q) ...) (net (r_1 R_1) ...) (net (p P) (r_2 R_2) ...))])

(define-metafunction Util
  join : N N -> N
  [(join (net) N) N]
  [(join N (net)) N]
  [(join (net (p P) (p_1 P_1) ...) (net (q Q) (q_1 Q_1) ...))
   (net (p P) (r R) ...)
   (side-condition (symbol<? (term p) (term q)))
   (where (net (r R) ...)
          (join (net (p_1 P_1) ...) (net (q Q) (q_1 Q_1) ...)))]
  [(join (net (p P) (p_1 P_1) ...) (net (q Q) (q_1 Q_1) ...))
   (net (q Q) (r R) ...)
   (side-condition (symbol<? (term q) (term p)))
   (where (net (r R) ...)
          (join (net (p P) (p_1 P_1) ...) (net (q_1 Q_1) ...)))])

;;; SimpleChor

(define-language SimpleChor
  (id ::= variable-not-otherwise-mentioned)
  ;; Choreographies
  (p q ::= id)
  (I ::= (p → q))
  (C ::= (chor I ...))
  ;; Transitions
  (μ ::= (p → q)))

;; (redex-match SimpleChor C (term (chor (p → q) (a → b))))
;; (term (pn (p → q)))

(define-judgment-form SimpleChor
  #:mode (smc→ I O O)
  #:contract (smc→ C μ C)
  [------------------------------------------------ com
   (smc→ (chor (p → q) I ...) (p → q) (chor I ...))]
  [(smc→ (chor I_1 ...) μ (chor I_2 ...))
   (side-condition ,(apply set-disjoint? (term ((pn I) (pn μ)))))
   -------------------------------------------------------------- delay
   (smc→ (chor I I_1 ...) μ (chor I I_2 ...))])

;; (judgment-holds (smc→ (chor (p → q) (r → s)) μ C) (μ C))
;; (show-derivations (build-derivations (smc→ (chor (p → q) (r → s)) μ C)))

(define SimpleChor->
  (reduction-relation
   SimpleChor
   #:domain C
   (--> C_1 C_2
        (judgment-holds (smc→ C_1 μ C_2))
        (computed-name (term (format-μ μ))))))

;; (apply-reduction-relation SimpleChor-> (term (chor (p → q) (p → r))))
;; (traces SimpleChor-> (term (chor (p → q) (p → r))))
;; (traces SimpleChor-> (term (chor (p → q) (r → q))))
;; (traces SimpleChor-> (term (chor (p → q) (r → s))))

;;; SimpleProc

(define-language SimpleProc
  (id ::= variable-not-otherwise-mentioned)
  ;; Processes
  (p q r ::= id)
  (I ::=
     (p !)
     (p ?))
  (P Q R ::= (proc I ...))
  ;; Networks
  (M N ::= (net (p P) ...))
  ;; Transitions
  (μ ::= (p → q)))

(define-judgment-form SimpleProc
  #:mode (smp→ I O O)
  #:contract (smp→ N μ N)
  [(commute N (net (p (proc (q !) I_1 ...)) (q (proc (p ?) I_2 ...))))
   ------------------------------------------------------------------- com
   (smp→ N (p → q) (make-net (p (proc I_1 ...)) (q (proc I_2 ...))))]
  [(split N M_1 M_2)
   (where (net _ _ ...) M_1)
   (where (net _ _ ...) M_2)
   (smp→ M_1 μ M_3)
   ------------------------- par
   (smp→ N μ (join M_2 M_3))])

(define-term N3-1
  (net (Client (proc (Gateway !)))
       (Gateway (proc (Client ?) (Server !)))
       (Server (proc (Gateway ?)))))

;; (judgment-holds (split (net) M_1 M_2) (M_1 M_2))
;; (judgment-holds (smp→ (net) μ N) (μ N))

;; (judgment-holds (split (net (p (proc (q !)))) M_1 M_2) (M_1 M_2))
;; (judgment-holds (smp→ (net (p (proc (q !)))) μ N) (μ N))

;; (judgment-holds (split (net (p (proc (q !))) (q (proc (p ?)))) M_1 M_2) (M_1 M_2))
;; (judgment-holds (smp→ (net (p (proc (q !))) (q (proc (p ?)))) μ M) (μ M))

;; (judgment-holds (split N3-1 M_1 M_2) (M_1 M_2))
;; (judgment-holds (smp→ N3-1 μ M) (μ M))
;; (show-derivations (build-derivations (smp→ N3-1 μ M)))

(define SimpleProc->
  (reduction-relation
   SimpleProc
   #:domain N
   (--> N_1 N_2
        (judgment-holds (smp→ N_1 μ N_2))
        (computed-name (term (format-μ μ))))))

;; (traces SimpleProc-> (term N3-1))
;; (stepper SimpleProc-> (term N3-1))

;;; StatefulChor

(define-extended-language StatefulChor SimpleChor
  ;; Expressions
  (v ::= any)
  (x ::= id)
  (f ::= id)
  (e ::= v x (f e ...))
  ;; Stores
  (σ ::= (pstore (x v) ...))
  (Σ ::= (cstore (p σ) ...))
  ;; Choreographies
  (I ::=
     (p e → q x)
     (p x := e))
  ;; Transitions
  (μ ::=
     (p v → q)
     (τ @ p))
  ;; Configurations
  (Conf ::= (conf C Σ)))

(define-judgment-form StatefulChor
  #:mode (stc→ I O O)
  #:contract (stc→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e v)
   ----------------------------------------------- local
   (stc→ (conf (chor (p x := e) I ...) Σ)
         (τ @ p)
         (conf (chor I ...) (put-var Σ (p (x v)))))]
  [(↓ (get-pstore Σ p) e v)
   ----------------------------------------------- com
   (stc→ (conf (chor (p e → q x) I ...) Σ)
         (p v → q)
         (conf (chor I ...) (put-var Σ (q (x v)))))]
  [(stc→ (conf (chor I_1 ...) Σ_1) μ (conf (chor I_2 ...) Σ_2))
   (side-condition ,(apply set-disjoint? (term ((pn I) (pn μ)))))
   ---------------------------------------------------------------- delay
   (stc→ (conf (chor I I_1 ...) Σ_1) μ (conf (chor I I_2 ...) Σ_2))])

(define (catalogue title)
  (case title
    [("My Choreographies") 100]
    [else (error 'catalogue "no book named ~s" title)]))

(define-term C5-6
  (chor (Buyer title → Seller x)
        (Seller (catalogue x) → Buyer price)))

(define-term Σ5-6
  (make-cstore (Buyer (title "My Choreographies"))))

;; (judgment-holds (stc→ (conf C5-6 Σ5-6) μ (conf C Σ)) (C Σ μ))
;; (judgment-holds (stc→ (conf (chor (r y := 4)) (cstore)) μ (conf C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (stc→ (conf (chor (r y := 4)) (cstore))
;;                                           μ (conf C Σ))))

(define StatefulChor->
  (reduction-relation
   StatefulChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (stc→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

;; (traces StatefulChor-> (term (conf C5-6 Σ5-6)))
;; (traces StatefulChor-> (term (conf (chor (p 5 → q x) (r y := 4)) (cstore))))

;;; StatefulProc

(define-extended-language StatefulProc SimpleProc
  ;; Expressions
  (v ::= any)
  (x ::= id)
  (f ::= id)
  (e ::= v x (f e ...))
  ;; Stores
  (σ ::= (pstore (x v) ...))
  (Σ ::= (cstore (p σ) ...))
  ;; Processes
  (I ::=
     (p ! e)
     (p ? x)
     (x := e))
  ;; Transitions
  (μ ::=
     (p v → q)
     (τ @ p))
  ;; Configurations
  (Conf ::= (conf N Σ)))

(define-judgment-form StatefulProc
  #:mode (stp→ I O O)
  #:contract (stp→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e v)
   ---------------------------------------------------------- local
   (stp→ (conf (net (p (proc (x := e) I ...))) Σ)
         (τ @ p)
         (conf (net (p (proc I ...))) (put-var Σ (p (x v)))))]
  [(commute N (net (p (proc (q ! e) I_1 ...)) (q (proc (p ? x) I_2 ...))))
   (↓ (get-pstore Σ p) e v)
   ----------------------------------------------------------------------- com
   (stp→ (conf N Σ)
         (p v → q)
         (conf (make-net (p (proc I_1 ...)) (q (proc I_2 ...)))
               (put-var Σ (q (x v)))))]
  [(split N M_1 M_2)
   (where (net _ _ ...) M_1)
   (where (net _ _ ...) M_2)
   (stp→ (conf M_1 Σ_1) μ (conf M_3 Σ_2))
   ----------------------------------------------- par
   (stp→ (conf N Σ_1) μ (conf (join M_2 M_3) Σ_2))])

;; (judgment-holds (stp→ (conf (make-net (p (proc (x := 6)))) (cstore)) μ Conf) (μ Conf))

(define-term N-ex-5-6
  (make-net (Buyer (proc (Seller ! title) (Seller ? price)))
            (Seller (proc (Buyer ? x) (Buyer ! (catalogue x))))))

;; (judgment-holds (stp→ (conf N-ex-5-6 (make-cstore (Buyer (title "My Choreographies")))) μ Conf) (μ Conf))

(define modpow modular-expt)

(define-term N-ex-5-7
  (make-net (Alice (proc (Bob ! (modpow g a p))
                         (Bob ? y)
                         (s := (modpow y a p))))
            (Bob (proc (Alice ? x)
                       (Alice ! (modpow g b p))
                       (s := (modpow x b p))))))

(define-term Σ-ex-5-7
  (make-cstore (Alice (p 23) (g 5) (a ,(random 10)))
               (Bob (p 23) (g 5) (b ,(random 10)))))

;; (judgment-holds (stp→ (conf N-ex-5-7 Σ-ex-5-7) μ Conf) (μ Conf))

(define StatefulProc->
  (reduction-relation
   StatefulProc
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (stp→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

;; (traces StatefulProc-> (term (conf N-ex-5-6 (put-var (cstore) (Buyer (title "My Choreographies"))))))
;; (traces StatefulProc-> (term (conf N-ex-5-7 Σ-ex-5-7)))

;;; ConditionalChor

(define-extended-language ConditionalChor StatefulChor
  ;; Choreographies
  (I ::=
     ....
     (if (p e) C_1 C_2)))

(define-overriding-judgment-form ConditionalChor stc→
  #:mode (coc→ I O O)
  #:contract (coc→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e #t)
   --------------------------------------------------------- cond-then
   (coc→ (conf (chor (if (p e) (chor I_1 ...) C_2) I ...) Σ)
         (τ @ p)
         (conf (chor I_1 ... I ...) Σ))]
  [(↓ (get-pstore Σ p) e #f)
   ----------------------------------------------------------- cond-else
   (coc→ (conf (chor (if (p e) C_1 (chor I_2 ...)) I ...) Σ)
         (τ @ p)
         (conf (chor I_2 ... I ...) Σ))]
  [(coc→ (conf C_1 Σ_1) μ (conf C_2 Σ_2))
   (coc→ (conf C_3 Σ_1) μ (conf C_4 Σ_2))
   (side-condition ,(apply set-disjoint? (term ((p) (pn μ)))))
   ----------------------------------------------------------- delay-cond
   (coc→ (conf (chor (if (p e) C_1 C_3) I ...) Σ_1)
         μ
         (conf (chor (if (p e) C_2 C_4) I ...) Σ_2))])

(define-term C6-2
  (chor (if (p (< x 10))
            (chor (q y := #t)
                  (p x := (+ x 1)))
            (chor (q y := #t)))))

(define-term Σ6-2
  (make-cstore (p (x 5)) (q (y #t))))

;; (judgment-holds (coc→ (conf C6-2 Σ6-2) μ (conf C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (coc→ (conf C6-2 Σ6-2) μ (conf C Σ))))

(define ConditionalChor->
  (reduction-relation
   ConditionalChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (coc→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

;; (traces ConditionalChor-> (term (conf C6-2 Σ6-2)))

;;; ConditionalProc

(define-extended-language ConditionalProc StatefulProc
  ;; Processes
  (I ::=
     ....
     (if e P Q)))

(define-overriding-judgment-form ConditionalProc stp→
  #:mode (cop→ I O O)
  #:contract (cop→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e #t)
   ------------------------------------------------------------ cond-then
   (cop→ (conf (net (p (proc (if e (proc I_1 ...) P) I ...))) Σ)
         (τ @ p)
         (conf (net (p (proc I_1 ... I ...))) Σ))]
  [(↓ (get-pstore Σ p) e #f)
   ------------------------------------------------------------ cond-else
   (cop→ (conf (net (p (proc (if e P (proc I_1 ...)) I ...))) Σ)
         (τ @ p)
         (conf (net (p (proc I_1 ... I ...))) Σ))])

(define-term N-ex-6-7
  (make-net (p (proc (if (< x 10)
                         (proc (x := (+ x 1)))
                         (proc))))
            (q (proc (y := #t) (r ! y)))
            (r (proc (q ? z)))))

(define-term Σ-ex-6-7
  (make-cstore (p (x 7))))

;; (judgment-holds (cop→ (conf N-ex-6-7 Σ-ex-6-7) μ Conf) (μ Conf))

(define ConditionalProc->
  (reduction-relation
   ConditionalProc
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (cop→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

;; (traces ConditionalProc-> (term (conf N-ex-6-7 Σ-ex-6-7)))

;;; SelectiveChor

(define-extended-language SelectiveChor ConditionalChor
  ;; Labels
  (l ::= id)
  ;; Choreographies
  (I ::=
     ....
     (p → q [l]))
  ;; Transitions
  (μ ::=
     ....
     (p → q [l])))

(define-overriding-judgment-form SelectiveChor coc→
  #:mode (slc→ I O O)
  #:contract (slc→ Conf μ Conf)
  [--------------------------------------- sel
   (slc→ (conf (chor (p → q [l]) I ...) Σ)
         (p → q [l])
         (conf (chor I ...) Σ))])

(define (timestamp)
  (date->string (current-date)))

(define-term C6-16
  (chor (Buyer title → Seller x)
        (Seller (catalogue x) → Buyer price)
        (if (Buyer (< price 150))
            (chor (Buyer → Seller [ok])
                  (Buyer address → Seller y)
                  (Seller (format "~a: ~a" y (timestamp)) → Buyer date))
            (chor (Buyer → Seller [ko])))))

(define-term Σ-ex-6-14
  (make-cstore (Buyer (title "My Choreographies")
                      (address "Internet Street"))))

;; (judgment-holds (slc→ (conf C6-16 Σ-ex-6-14) μ (conf C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (slc→ (conf C6-16 Σ-ex-6-14) μ (conf C Σ))))
;; (show-derivations
;;  (build-derivations
;;   (slc→ (conf (chor (if (p e)
;;                        (chor (q → r [ok])
;;                              (q x := 4))
;;                        (chor (q → r [ok])
;;                              (r x := 5))))
;;              (cstore))
;;        μ (conf C Σ))))

(define SelectiveChor->
  (reduction-relation
   SelectiveChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (slc→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

;; (traces SelectiveChor-> (term (conf C6-16 Σ-ex-6-14)))
;; (traces SelectiveChor-> (term (conf (chor (p → q [ok])) (cstore))))

;;; SelectiveProc

(define-extended-language SelectiveProc ConditionalProc
  ;; Labels
  (l ::= id)
  ;; Processes
  (I ::=
     ....
     (p ⊕ l)
     (p & (l P) ...))
  ;; Transitions
  (μ ::=
     ....
     (p → q [l])))

(define-overriding-judgment-form SelectiveProc cop→
  #:mode (slp→ I O O)
  #:contract (slp→ Conf μ Conf)
  [(commute N (net (p (proc (q ⊕ l) I_1 ...))
                   (q (proc (p & (l_1 P_1) ...) I_2 ...))))
   (where (_ ... (l (proc I_3 ...)) _ ...) ((l_1 P_1) ...))
   ------------------------------------------------------------------------ sel
   (slp→ (conf N Σ)
         (p → q [l])
         (conf (make-net (p (proc I_1 ...)) (q (proc I_3 ... I_2 ...))) Σ))])

(define (valid-creds? creds)
  (equal? creds "secret"))

(define (new-token)
  "totally-unique-token")

(define-term N-ex-6-15
  (make-net (c (proc (cas ! creds)
                     (s &
                        (token (proc (s ? t)))
                        (error (proc)))))
            (s (proc (cas &
                          (ok (proc (c ⊕ token)
                                    (c ! (new-token))))
                          (ko (proc (c ⊕ error))))))
            (cas (proc (c ? x)
                       (if (valid-creds? x)
                           (proc (s ⊕ ok))
                           (proc (s ⊕ ko)))))))

(define-term Σ-ex-6-17-1
  (make-cstore (c (creds "secret"))))

(define-term Σ-ex-6-17-2
  (make-cstore (c (creds "wrong"))))

;; (judgment-holds (slp→ (conf N-ex-6-15 Σ-ex-6-17-1) μ Conf) (μ Conf))
;; (show-derivations (build-derivations (slp→ (conf N-ex-6-15 Σ-ex-6-17-1) μ Conf)))

(define SelectiveProc->
  (reduction-relation
   SelectiveProc
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (slp→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

;; (traces SelectiveProc-> (term (conf N-ex-6-15 Σ-ex-6-17-1)))
;; (traces SelectiveProc-> (term (conf N-ex-6-15 Σ-ex-6-17-2)))

;;; RecursiveChor

(define-extended-language RecursiveChor SelectiveChor
  ;; Definitions
  (X ::= id)
  (D ::= (defs (X ((p ...) C)) ...))
  ;; Choreographies
  (I ::=
     ....
     (X p ...)
     (enter (p ...) (X p ...) C))
  ;; Configurations
  (Conf ::= (conf C Σ D)))

(define-judgment-form RecursiveChor
  #:mode (rcc→ I O O)
  #:contract (rcc→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e v)
   ------------------------------------------------- local
   (rcc→ (conf (chor (p x := e) I ...) Σ D)
         (τ @ p)
         (conf (chor I ...) (put-var Σ (p (x v))) D))]
  [(↓ (get-pstore Σ p) e v)
   ------------------------------------------------- com
   (rcc→ (conf (chor (p e → q x) I ...) Σ D)
         (p v → q)
         (conf (chor I ...) (put-var Σ (q (x v))) D))]
  [---------------------------------------- sel
   (rcc→ (conf (chor (p → q [l]) I ...) Σ D)
         (p → q [l])
         (conf (chor I ...) Σ D))]
  [(↓ (get-pstore Σ p) e #t)
   ----------------------------------------------------------- cond-then
   (rcc→ (conf (chor (if (p e) (chor I_1 ...) C_2) I ...) Σ D)
         (τ @ p)
         (conf (chor I_1 ... I ...) Σ D))]
  [(↓ (get-pstore Σ p) e #f)
   ----------------------------------------------------------- cond-else
   (rcc→ (conf (chor (if (p e) C_1 (chor I_2 ...)) I ...) Σ D)
         (τ @ p)
         (conf (chor I_2 ... I ...) Σ D))]
  [(where ((q ...) (chor I_1 ...)) (get-def D X))
   (where (p_1 ... p_2 p_3 ...) (p ...))
   ------------------------------------------------------------------ call-first
   (rcc→ (conf (chor (X p ...) I ...) Σ D)
         (τ @ p_2)
         (conf (chor (enter (p_1 ... p_3 ...) (X p ...) (chor I ...))
                     (subst I_1 (q p) ...) ...
                     I ...)
               Σ D))]
  [(where (q_1 ... q_2 q_3 ...) (q ...))
   (side-condition ,(> (length (term (q ...))) 1))
   -------------------------------------------------------------------- call-enter
   (rcc→ (conf (chor (enter (q ...) (X p ...) C) I ...) Σ D)
         (τ @ q_2)
         (conf (chor (enter (q_1 ... q_3 ...) (X p ...) C) I ...) Σ D))]
  [----------------------------------------------------- call-last
   (rcc→ (conf (chor (enter (q) (X p ...) C) I ...) Σ D)
         (τ @ q)
         (conf (chor I ...) Σ D))]
  [(rcc→ (conf (chor I_1 ...) Σ_1 D) μ (conf (chor I_2 ...) Σ_2 D))
   (side-condition ,(apply set-disjoint? (term ((pn I) (pn μ)))))
   -------------------------------------------------------------------- delay
   (rcc→ (conf (chor I I_1 ...) Σ_1 D) μ (conf (chor I I_2 ...) Σ_2 D))]
  [(rcc→ (conf C_1 Σ_1 D) μ (conf C_2 Σ_2 D))
   (rcc→ (conf C_3 Σ_1 D) μ (conf C_4 Σ_2 D))
   (side-condition ,(apply set-disjoint? (term ((p) (pn μ)))))
   ----------------------------------------------------------- delay-cond
   (rcc→ (conf (chor (if (p e) C_1 C_3) I ...) Σ_1 D)
         μ
         (conf (chor (if (p e) C_2 C_4) I ...) Σ_2 D))])

(define RecursiveChor->
  (reduction-relation
   RecursiveChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (rcc→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

(define-term C-ping
  (chor (Ping Alice Bob)))

(define-term D-ping
  (make-defs ((Ping p q) (chor (p → q [sig]) (Ping p q)))))

;; (traces RecursiveChor-> (term (conf C-ping (cstore) D-ping)))

(define-term C-ping-pong
  (chor (Alice → Bob [sig]) (PP Alice Bob)))

(define-term D-ping-pong
  (make-defs ((PP p q) (chor (p → q [sig]) (PP q p)))))

;; (traces RecursiveChor-> (term (conf C-ping-pong (cstore) D-ping-pong)))

(define (make-packet file n)
  (list (list-ref file (sub1 n))))

(define (read-file filename)
  (case filename
    [("motd") (list "hello" "there" "world")]
    [else (error 'read-file "no file named ~s" filename)]))

(define empty-file list)
(define packets length)
(define crc identity)

(define-term C7-2
  (chor (downloader "motd" → storage filename)
        (storage file := (read-file filename))
        (downloader file := (empty-file))
        (storage n := 1)
        (S downloader storage)
        (storage (crc file) → downloader crc-orig)
        (downloader ok := (equal? (crc file) crc-orig))))

(define-term D7-2
  (make-defs ((S c s)
              (chor (if (s (<= n (packets file)))
                        (chor (s → c [next])
                              (s (make-packet file n) → c packet)
                              (c file := (append file packet))
                              (s n := (+ n 1))
                              (S c s))
                        (chor (s → c [end])))))))

;; (traces RecursiveChor-> (term (conf C7-2 (cstore) D7-2)))

(define-judgment-form RecursiveChor
  #:mode (rcc-wf-c I O I)
  #:contract (rcc-wf-c D (p ...) C)
  [---------------------- wf-end
   (rcc-wf-c _ () (chor))]
  [(rcc-wf-c D (p_1 ...) (chor I ...))
   (side-condition (not (apply equal? (term (p q)))))
   (where (p_2 ...) ,(apply set-union (term ((p q) (p_1 ...)))))
   ------------------------------------------------------------- wf-com
   (rcc-wf-c D (p_2 ...) (chor (p e → q x) I ...))]
  [(rcc-wf-c D (p_1 ...) (chor I ...))
   (side-condition (not (apply equal? (term (p q)))))
   (where (p_2 ...) ,(apply set-union (term ((p q) (p_1 ...)))))
   ------------------------------------------------------------- wf-sel
   (rcc-wf-c D (p_2 ...) (chor (p → q [l]) I ...))]
  [(rcc-wf-c D (p_1 ...) (chor I ...))
   (where (p_2 ...) ,(apply set-union (term ((p) (p_1 ...)))))
   ----------------------------------------------------------- wf-local
   (rcc-wf-c D (p_2 ...) (chor (p x := e) I ...))]
  [(rcc-wf-c D (p_1 ...) C_1)
   (rcc-wf-c D (p_2 ...) C_2)
   (rcc-wf-c D (p_3 ...) (chor I ...))
   (where (p_4 ...)
          ,(apply set-union (term ((p) (p_1 ...) (p_2 ...) (p_3 ...)))))
   --------------------------------------------------------------------- wf-cond
   (rcc-wf-c D (p_4 ...) (chor (if (p e) C_1 C_2) I ...))]
  [(where ((q ...) _) (get-def D X))
   (rcc-wf-c D (p_1 ...) (chor I ...))
   (side-condition ,(= (length (term (p ...))) (length (term (q ...)))))
   (side-condition ,(not (check-duplicates (term (p ...)))))
   (where (p_2 ...) ,(apply set-union (term ((p ...) (p_1 ...)))))
   --------------------------------------------------------------------- wf-call
   (rcc-wf-c D (p_2 ...) (chor (X p ...) I ...))])

(define-judgment-form RecursiveChor
  #:mode (rcc-wf-d I O)
  #:contract (rcc-wf-d D ((X (p ...)) ...))
  [(rcc-wf-c D (p ...) C)
   ...
   (side-condition ,(andmap (compose not check-duplicates)
                            (term ((q ...) ...))))
   (side-condition ,(andmap (applify subset?) (term (((p ...) (q ...)) ...))))
   (side-condition ,(andmap (compose (partial < 1) length)
                            (term ((q ...) ...))))
   ---------------------------------------------------------------------------
   (rcc-wf-d (name D (defs (X ((q ...) C)) ...)) ((X (p ...)) ...))])

(define-judgment-form RecursiveChor
  #:mode (rcc-wf-f I O)
  #:contract (rcc-wf-f Conf (p ...))
  [(rcc-wf-c D (p ...) C)
   (rcc-wf-d D _)
   ------------------------------
   (rcc-wf-f (conf C _ D) (p ...))])

;; (judgment-holds (rcc-wf-c D-ping any C-ping) any)
;; (judgment-holds (rcc-wf-d D-ping any) any)
;; (judgment-holds (rcc-wf-d (defs (X ((p) (chor (p x := e))))) any) any)
;; (judgment-holds (rcc-wf-f (conf C-ping (cstore) D-ping) any) any)

;;; RecursiveProc

(define-extended-language RecursiveProc SelectiveProc
  ;; Definitions
  (X ::= id)
  (D ::= (defs (X ((p ...) P)) ...))
  ;; Processes
  (I ::=
     ....
     (X p ...))
  ;; Configurations
  (Conf ::= (conf N Σ D)))

(define-overriding-judgment-form RecursiveProc slp→
  #:mode (rcp→ I O O)
  #:contract (rcp→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e v)
   ------------------------------------------------------------ local
   (rcp→ (conf (net (p (proc (x := e) I ...))) Σ D)
         (τ @ p)
         (conf (net (p (proc I ...))) (put-var Σ (p (x v))) D))]
  [(commute N (net (p (proc (q ⊕ l) I_1 ...))
                   (q (proc (p & (l_1 P_1) ...) I_2 ...))))
   (where (_ ... (l (proc I_3 ...)) _ ...) ((l_1 P_1) ...))
   -------------------------------------------------------------------------- sel
   (rcp→ (conf N Σ D)
         (p → q [l])
         (conf (make-net (p (proc I_1 ...)) (q (proc I_3 ... I_2 ...))) Σ D))]
  [(commute N (net (p (proc (q ! e) I_1 ...)) (q (proc (p ? x) I_2 ...))))
   (↓ (get-pstore Σ p) e v)
   ----------------------------------------------------------------------- com
   (rcp→ (conf N Σ D)
         (p v → q)
         (conf (make-net (p (proc I_1 ...)) (q (proc I_2 ...)))
               (put-var Σ (q (x v)))
               D))]
  [(↓ (get-pstore Σ p) e #t)
   --------------------------------------------------------------- cond-then
   (rcp→ (conf (net (p (proc (if e (proc I_1 ...) P) I ...))) Σ D)
         (τ @ p)
         (conf (net (p (proc I_1 ... I ...))) Σ D))]
  [(↓ (get-pstore Σ p) e #f)
   --------------------------------------------------------------- cond-else
   (rcp→ (conf (net (p (proc (if e P (proc I_1 ...)) I ...))) Σ D)
         (τ @ p)
         (conf (net (p (proc I_1 ... I ...))) Σ D))]
  [(where ((r ...) (proc I_1 ...)) (get-def D X))
   ------------------------------------------------------------------ call
   (rcp→ (conf (net (p (proc (X q ...) I ...))) Σ D)
         (τ @ p)
         (conf (net (p (proc (subst I_1 (r q) ...) ... I ...))) Σ D))]
  [(split N M_1 M_2)
   (where (net _ _ ...) M_1)
   (where (net _ _ ...) M_2)
   (rcp→ (conf M_1 Σ_1 D) μ (conf M_3 Σ_2 D))
   --------------------------------------------------- par
   (rcp→ (conf N Σ_1 D) μ (conf (join M_2 M_3) Σ_2 D))])

(define-term D-ex-7-13
  (make-defs ((PP_1 q) (proc (q ⊕ sig) (PP_2 q)))
             ((PP_2 p) (proc (p & (sig (proc (PP_1 p))))))))

(define-term N-ex-7-13
  (make-net (Alice (proc (PP_1 Bob))) (Bob (proc (PP_2 Alice)))))

;; (judgment-holds (rcp→ (conf N-ex-6-15 Σ-ex-6-17-1 (defs)) μ Conf) (μ Conf))
;; (show-derivations (build-derivations (rcp→ (conf N-ex-6-15 Σ-ex-6-17-1 (defs)) μ Conf)))

;; (judgment-holds (rcp→ (conf (make-net (p (proc (X p))))
;;                             (cstore)
;;                             (make-defs ((X p) (proc (X p)))))
;;                       μ Conf) (μ Conf))

;; (judgment-holds (rcp→ (conf N-ex-7-13 (cstore) D-ex-7-13) μ Conf) (μ Conf))

(define RecursiveProc->
  (reduction-relation
   RecursiveProc
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (rcp→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

;; (traces RecursiveProc-> (term (conf N-ex-7-13 (cstore) D-ex-7-13)))

;;; Choreographic Choice

(define-extended-language ChoiceChor RecursiveChor
  ;; Choreographies
  (I ::=
     ....
     (C + p C)))

(define-extended-judgment-form ChoiceChor rcc→
  #:mode (chc→ I O O)
  #:contract (chc→ Conf μ Conf)
  [(chc→ (conf C_1 Σ D) μ (conf (chor I_′ ...) Σ_′ D))
   (side-condition ,(apply set-member? (term ((pn μ) p))))
   ------------------------------------------------------- choice-l
   (chc→ (conf (chor (C_1 + p C_2) I ...) Σ D)
         μ
         (conf (chor I_′ ... I ... ) Σ_′ D))]
  [(chc→ (conf C_2 Σ D) μ (conf (chor I_′ ...) Σ_′ D))
   (side-condition ,(apply set-member? (term ((pn μ) p))))
   ------------------------------------------------------- choice-r
   (chc→ (conf (chor (C_1 + p C_2) I ...) Σ D)
         μ
         (conf (chor I_′ ... I ... ) Σ_′ D))]
  [(chc→ (conf C_1 Σ D) μ (conf C_1′ Σ_′ D))
   (chc→ (conf C_2 Σ D) μ (conf C_2′ Σ_′ D))
   (side-condition ,(apply (compose not set-member?) (term ((pn μ) p))))
   --------------------------------------------------------------------- delay-choice
   (chc→ (conf (chor (C_1 + p C_2) I ...) Σ D)
         μ
         (conf (chor (C_1′ + p C_2′) I ...) Σ_′ D))])

(define ChoiceChor->
  (reduction-relation
   ChoiceChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (chc→ Conf_1 μ Conf_2))
        (computed-name (term (format-μ μ))))))

(define-term C-10-5
  ,(term-let ([C_1 (term (chor (Bob news → Alice x)
                               (Carol news → Alice y)))]
              [C_2 (term (chor (Carol news → Alice y)
                               (Bob news → Alice x)))])
             (term (chor (Bob news := "bob")
                         (Carol news := "carol")
                         (C_1 + Alice C_2)))))

;; (traces ChoiceChor-> (term (conf C-10-5 (cstore) (defs))))
;; (show-derivations (build-derivations (chc→ (conf C-10-5 (cstore) (defs)) μ Conf)))
