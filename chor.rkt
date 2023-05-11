#lang racket

(require racket/set)
(require racket/date)
(require redex)

;; * Abbreviations
;;
;; - chor -- choreography
;; - cstore -- choreographic store
;; - pstore -- process store
;; - dstore -- set of definitions (procedures)
;; - conf -- configuration
;;
;; - sc -- Simple Choreographies
;; - st -- Stateful Choreographies
;; - cc -- Conditional Choreographies
;; - sl -- Selective Choreographies
;; - rc -- Recursive Choreographies
;;
;; - wf -- well-formed
;; - pn -- process names
;; - p -- process
;; - i -- instruction
;; - c -- choreography
;; - d -- definition
;; - f -- configuration

;; * TODO
;;
;; - Proper tests. Small examples are in the comments below.
;;
;; - Chapter 10.
;;
;; - Well-formedness for the runtime term.

;;; Util

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

;;; SimpleChor

(define-language SimpleChor
  (id ::= variable-not-otherwise-mentioned)
  ;; Choreographies
  (p q ::= id)
  (I ::= (p → q))
  (C ::= (chor I ...))
  ;; Transitions
  (μ ::= (p → q)))

(define-metafunction SimpleChor
  sc-pn-i : I -> (p ...)
  [(sc-pn-i (p → q)) (p q)])

(define-metafunction SimpleChor
  sc-pn-μ : μ -> (p ...)
  [(sc-pn-μ (p → q)) (p q)])

;; (redex-match SimpleChor C (term (chor (p → q) (a → b))))
;; (term (sc-pn-i (p → q)))

(define-judgment-form SimpleChor
  #:mode (sc→ I O O)
  #:contract (sc→ C μ C)
  [----------------------------------------------- com
   (sc→ (chor (p → q) I ...) (p → q) (chor I ...))]
  [(sc→ (chor I_1 ...) μ (chor I_2 ...))
   (side-condition ,(apply set-disjoint? (term ((sc-pn-i I) (sc-pn-μ μ)))))
   ------------------------------------------------------------------------ delay
   (sc→ (chor I I_1 ...) μ (chor I I_2 ...))])

;; (judgment-holds (sc→ (chor (p → q) (r → s)) μ C) (μ C))
;; (show-derivations (build-derivations (sc→ (chor (p → q) (r → s)) μ C)))

(define-metafunction SimpleChor
  sc-format-μ : μ -> string
  [(sc-format-μ (p → q)) ,(apply format "~a → ~a" (term (p q)))])

(define SimpleChor->
  (reduction-relation
   SimpleChor
   #:domain C
   (--> C_1 C_2
        (judgment-holds (sc→ C_1 μ C_2))
        (computed-name (term (sc-format-μ μ))))))

;; (apply-reduction-relation SimpleChor-> (term (chor (p → q) (p → r))))
;; (traces SimpleChor-> (term (chor (p → q) (p → r))))
;; (traces SimpleChor-> (term (chor (p → q) (r → q))))
;; (traces SimpleChor-> (term (chor (p → q) (r → s))))

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

(define (assoc-store k store [default (void)])
  (match store
    [`(,(or 'cstore 'pstore 'dstore) . ,alist)
     (let ([v (assoc k alist)])
       (if v (second v) default))]))

(define (put-store k v store)
  (match store
    [`(,(and store (or 'cstore 'pstore 'dstore)) . ,alist)
     `(,store ,@(aput k (list v) alist #:less? symbol<?))]))

(define-metafunction StatefulChor
  get-var : σ x -> (boolean v)
  [(get-var σ x)
   (#t v)
   (where v ,(apply assoc-store (term (x σ))))
   (side-condition (not (equal? (term v) (void))))]
  [(get-var _ _) (#f 42)])

(define (eval-safe f args)
  (with-handlers ([exn:fail? (lambda (v)
                               ((error-display-handler) (exn-message v) v)
                               (list #f 42))])
    (list #t (apply (eval f) args))))

(define-judgment-form StatefulChor
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

(define-metafunction StatefulChor
  get-pstore : Σ p -> σ
  [(get-pstore Σ p) ,(apply assoc-store (term (p Σ (pstore))))])

(define-metafunction StatefulChor
  put-var : Σ p x v -> Σ
  [(put-var Σ p x v)
   ,(apply put-store (term (p σ Σ)))
   (where σ_1 (get-pstore Σ p))
   (where σ ,(apply put-store (term (x v σ_1))))])

(define-metafunction StatefulChor
  st-pn-i : I -> (p ...)
  [(st-pn-i (p e → q x)) (p q)]
  [(st-pn-i (p x := e)) (p)])

(define-metafunction StatefulChor
  st-pn-μ : μ -> (p ...)
  [(st-pn-μ (p v → q)) (p q)]
  [(st-pn-μ (τ @ p)) (p)])

(define-judgment-form StatefulChor
  #:mode (st→ I O O)
  #:contract (st→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e v)
   ------------------------------------------- local
   (st→ (conf (chor (p x := e) I ...) Σ)
        (τ @ p)
        (conf (chor I ...) (put-var Σ p x v)))]
  [(↓ (get-pstore Σ p) e v)
   ------------------------------------------- com
   (st→ (conf (chor (p e → q x) I ...) Σ)
        (p v → q)
        (conf (chor I ...) (put-var Σ q x v)))]
  [(st→ (conf (chor I_1 ...) Σ_1) μ (conf (chor I_2 ...) Σ_2))
   (side-condition ,(apply set-disjoint? (term ((st-pn-i I) (st-pn-μ μ)))))
   ------------------------------------------------------------------------ delay
   (st→ (conf (chor I I_1 ...) Σ_1) μ (conf (chor I I_2 ...) Σ_2))])

(define (catalogue title)
  (case title
    [("My Choreographies") 100]
    [else (error 'catalogue "no book named ~s" title)]))

(define-term C5-6
  (chor (Buyer title → Seller x)
        (Seller (catalogue x) → Buyer price)))

(define-term Σ5-6
  (put-var (cstore) Buyer title "My Choreographies"))

;; (judgment-holds (st→ (conf C5-6 Σ5-6) μ (conf C Σ)) (C Σ μ))
;; (judgment-holds (st→ (conf (chor (r y := 4)) (cstore)) μ (conf C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (st→ (conf (chor (r y := 4)) (cstore))
;;                                           μ (conf C Σ))))

(define-metafunction StatefulChor
  st-format-μ : μ -> string
  [(st-format-μ (p v → q)) ,(apply format "~a.~s → ~a" (term (p v q)))]
  [(st-format-μ (τ @ p)) ,(format "τ@~a" (term p))])

(define StatefulChor->
  (reduction-relation
   StatefulChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (st→ Conf_1 μ Conf_2))
        (computed-name (term (st-format-μ μ))))))

;; (traces StatefulChor-> (term (conf C5-6 Σ5-6)))
;; (traces StatefulChor-> (term (conf (chor (p 5 → q x) (r y := 4)) (cstore))))

;;; ConditionalChor

(define-extended-language ConditionalChor StatefulChor
  ;; Choreographies
  (I ::=
     ....
     (if (p e) C_1 C_2)))

(define-metafunction/extension st-pn-i ConditionalChor
  cc-pn-i : I -> (p ...)
  [(cc-pn-i (if (p e) (chor I_1 ...) (chor I_2 ...)))
   ,(apply set-union (term ((p) (cc-pn-i I_1) ... (cc-pn-i I_2) ...)))])

(define-overriding-judgment-form ConditionalChor st→
  #:mode (cc→ I O O)
  #:contract (cc→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e #t)
   -------------------------------------------------------- cond-then
   (cc→ (conf (chor (if (p e) (chor I_1 ...) C_2) I ...) Σ)
        (τ @ p)
        (conf (chor I_1 ... I ...) Σ))]
  [(↓ (get-pstore Σ p) e #f)
   ----------------------------------------------------------- cond-else
   (cc→ (conf (chor (if (p e) C_1 (chor I_2 ...)) I ...) Σ)
        (τ @ p)
        (conf (chor I_2 ... I ...) Σ))]
  [(cc→ (conf (chor I_1 ...) Σ_1) μ (conf (chor I_2 ...) Σ_2))
   (side-condition ,(apply set-disjoint? (term ((cc-pn-i I) (st-pn-μ μ)))))
   ------------------------------------------------------------------------ delay
   (cc→ (conf (chor I I_1 ...) Σ_1) μ (conf (chor I I_2 ...) Σ_2))]
  [(cc→ (conf C_1 Σ_1) μ (conf C_2 Σ_2))
   (cc→ (conf C_3 Σ_1) μ (conf C_4 Σ_2))
   (side-condition ,(apply set-disjoint? (term ((p) (st-pn-μ μ)))))
   ---------------------------------------------------------------- delay-cond
   (cc→ (conf (chor (if (p e) C_1 C_3) I ...) Σ_1)
        μ
        (conf (chor (if (p e) C_2 C_4) I ...) Σ_2))])

(define-term C6-2
  (chor (if (p (< x 10))
            (chor (q y := #t)
                  (p x := (+ x 1)))
            (chor (q y := #t)))))

(define-term Σ6-2
  (put-var (put-var (cstore) p x 5) q y #t))

;; (judgment-holds (cc→ (conf C6-2 Σ6-2) μ (conf C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (cc→ (conf C6-2 Σ6-2) μ (conf C Σ))))

(define ConditionalChor->
  (reduction-relation
   ConditionalChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (cc→ Conf_1 μ Conf_2))
        (computed-name (term (st-format-μ μ))))))

;; (traces ConditionalChor-> (term (conf C6-2 Σ6-2)))

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

(define-metafunction/extension cc-pn-i SelectiveChor
  sl-pn-i : I -> (p ...)
  [(sl-pn-i (p → q [l])) (p q)])

(define-metafunction/extension st-pn-μ SelectiveChor
  sl-pn-μ : μ -> (p ...)
  [(sl-pn-μ (p → q [l])) (p q)])

(define-overriding-judgment-form SelectiveChor cc→
  #:mode (sl→ I O O)
  #:contract (sl→ Conf μ Conf)
  [-------------------------------------- sel
   (sl→ (conf (chor (p → q [l]) I ...) Σ)
        (p → q [l])
        (conf (chor I ...) Σ))]
  [(sl→ (conf (chor I_1 ...) Σ_1) μ (conf (chor I_2 ...) Σ_2))
   (side-condition ,(apply set-disjoint? (term ((sl-pn-i I) (sl-pn-μ μ)))))
   ------------------------------------------------------------------------ delay
   (sl→ (conf (chor I I_1 ...) Σ_1) μ (conf (chor I I_2 ...) Σ_2))]
  [(sl→ (conf C_1 Σ_1) μ (conf C_2 Σ_2))
   (sl→ (conf C_3 Σ_1) μ (conf C_4 Σ_2))
   (side-condition ,(apply set-disjoint? (term ((p) (sl-pn-μ μ)))))
   ---------------------------------------------------------------- delay-cond
   (sl→ (conf (chor (if (p e) C_1 C_3) I ...) Σ_1)
        μ
        (conf (chor (if (p e) C_2 C_4) I ...) Σ_2))])

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

(define-term Σ6-16
  (put-var (put-var (cstore) Buyer title "My Choreographies")
              Buyer address "Internet Street"))

;; (judgment-holds (sl→ (conf C6-16 Σ6-16) μ (conf C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (sl→ (conf C6-16 Σ6-16) μ (conf C Σ))))
;; (show-derivations
;;  (build-derivations
;;   (sl→ (conf (chor (if (p e)
;;                        (chor (q → r [ok])
;;                              (q x := 4))
;;                        (chor (q → r [ok])
;;                              (r x := 5))))
;;              (cstore))
;;        μ (conf C Σ))))

(define-metafunction/extension st-format-μ SelectiveChor
  sl-format-μ : μ -> string
  [(sl-format-μ (p → q [l])) ,(apply format "~a → ~a [~a]" (term (p q l)))])

(define SelectiveChor->
  (reduction-relation
   SelectiveChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (sl→ Conf_1 μ Conf_2))
        (computed-name (term (sl-format-μ μ))))))

;; (traces SelectiveChor-> (term (conf C6-16 Σ6-16)))
;; (traces SelectiveChor-> (term (conf (chor (p → q [ok])) (cstore))))

;;; RecursiveChor

(define-extended-language RecursiveChor SelectiveChor
  ;; Definitions
  (X ::= id)
  (D ::= (dstore (X ((p ...) C)) ...))
  ;; Choreographies
  (I ::=
     ....
     (X p ...)
     (enter (p ...) (X p ...) C))
  ;; Configurations
  (Conf ::= (conf C Σ D)))

(define-metafunction RecursiveChor
  subst-p : p (p p) ... -> p
  [(subst-p p (p_1 q_1) ... (p q) (p_2 q_2) ...) q]
  [(subst-p p _ ...) p])

(define-metafunction RecursiveChor
  subst-i : I (p p) ... -> I
  [(subst-i (p e → q x) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) e → (subst-p q (p_1 q_1) ...) x)]
  [(subst-i (p x := e) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) x := e)]
  [(subst-i (if (p e) (chor I_1 ...) (chor I_2 ...)) (p_1 q_1) ...)
   (if ((subst-p p (p_1 q_1) ...) e)
       (chor (subst-i I_1 (p_1 q_1) ...) ...)
       (chor (subst-i I_2 (p_1 q_1) ...) ...))]
  [(subst-i (p → q [l]) (p_1 q_1) ...)
   ((subst-p p (p_1 q_1) ...) → (subst-p q (p_1 q_1) ...) [l])]
  [(subst-i (X p ...) (p_1 q_1) ...)
   (X (subst-p p (p_1 q_1) ...) ...)])

(define-metafunction/extension sl-pn-i RecursiveChor
  rc-pn-i : I -> (p ...)
  [(rc-pn-i (X p ...)) (p ...)]
  [(rc-pn-i (enter (q ...) _ _)) (q ...)])

(define-metafunction RecursiveChor
  get-def : D X -> ((p ...) C)
  [(get-def D X) ,(apply assoc-store (term (X D)))])

(define-metafunction RecursiveChor
  put-def : D (X p ...) C -> D
  [(put-def D (X p ...) C) ,(apply put-store (term (X ((p ...) C) D)))])

(define-judgment-form RecursiveChor
  #:mode (rc→ I O O)
  #:contract (rc→ Conf μ Conf)
  [(↓ (get-pstore Σ p) e v)
   --------------------------------------------- local
   (rc→ (conf (chor (p x := e) I ...) Σ D)
        (τ @ p)
        (conf (chor I ...) (put-var Σ p x v) D))]
  [(↓ (get-pstore Σ p) e v)
   --------------------------------------------- com
   (rc→ (conf (chor (p e → q x) I ...) Σ D)
        (p v → q)
        (conf (chor I ...) (put-var Σ q x v) D))]
  [---------------------------------------- sel
   (rc→ (conf (chor (p → q [l]) I ...) Σ D)
        (p → q [l])
        (conf (chor I ...) Σ D))]
  [(↓ (get-pstore Σ p) e #t)
   ---------------------------------------------------------- cond-then
   (rc→ (conf (chor (if (p e) (chor I_1 ...) C_2) I ...) Σ D)
        (τ @ p)
        (conf (chor I_1 ... I ...) Σ D))]
  [(↓ (get-pstore Σ p) e #f)
   ----------------------------------------------------------- cond-else
   (rc→ (conf (chor (if (p e) C_1 (chor I_2 ...)) I ...) Σ D)
        (τ @ p)
        (conf (chor I_2 ... I ...) Σ D))]
  [(where ((q ...) (chor I_1 ...)) (get-def D X))
   (where (p_1 ... p_2 p_3 ...) (p ...))
   ----------------------------------------------------------------- call-first
   (rc→ (conf (chor (X p ...) I ...) Σ D)
        (τ @ p_2)
        (conf (chor (enter (p_1 ... p_3 ...) (X p ...) (chor I ...))
                    (subst-i I_1 (q p) ...) ...
                    I ...)
              Σ D))]
  [(where (q_1 ... q_2 q_3 ...) (q ...))
   (side-condition ,(> (length (term (q ...))) 1))
   ------------------------------------------------------------------- call-enter
   (rc→ (conf (chor (enter (q ...) (X p ...) C) I ...) Σ D)
        (τ @ q_2)
        (conf (chor (enter (q_1 ... q_3 ...) (X p ...) C) I ...) Σ D))]
  [---------------------------------------------------- call-last
   (rc→ (conf (chor (enter (q) (X p ...) C) I ...) Σ D)
        (τ @ q)
        (conf (chor I ...) Σ D))]
  [(rc→ (conf (chor I_1 ...) Σ_1 D) μ (conf (chor I_2 ...) Σ_2 D))
   (side-condition ,(apply set-disjoint? (term ((rc-pn-i I) (sl-pn-μ μ)))))
   ------------------------------------------------------------------------ delay
   (rc→ (conf (chor I I_1 ...) Σ_1 D) μ (conf (chor I I_2 ...) Σ_2 D))]
  [(rc→ (conf C_1 Σ_1 D) μ (conf C_2 Σ_2 D))
   (rc→ (conf C_3 Σ_1 D) μ (conf C_4 Σ_2 D))
   (side-condition ,(apply set-disjoint? (term ((p) (sl-pn-μ μ)))))
   ---------------------------------------------------------------- delay-cond
   (rc→ (conf (chor (if (p e) C_1 C_3) I ...) Σ_1 D)
        μ
        (conf (chor (if (p e) C_2 C_4) I ...) Σ_2 D))])

(define RecursiveChor->
  (reduction-relation
   RecursiveChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (rc→ Conf_1 μ Conf_2))
        (computed-name (term (sl-format-μ μ))))))

(define-term C-ping
  (chor (Ping Alice Bob)))

(define-term D-ping
  (put-def (dstore) (Ping p q) (chor (p → q [sig]) (Ping p q))))

;; (traces RecursiveChor-> (term (conf C-ping (cstore) D-ping)))

(define-term C-ping-pong
  (chor (Alice → Bob [sig]) (PP Alice Bob)))

(define-term D-ping-pong
  (put-def (dstore) (PP p q) (chor (p → q [sig]) (PP q p))))

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
  (put-def (dstore)
           (S c s)
           (chor (if (s (<= n (packets file)))
                     (chor (s → c [next])
                           (s (make-packet file n) → c packet)
                           (c file := (append file packet))
                           (s n := (+ n 1))
                           (S c s))
                     (chor (s → c [end]))))))

;; (traces RecursiveChor-> (term (conf C7-2 (cstore) D7-2)))

(define-judgment-form RecursiveChor
  #:mode (rc-wf-c I O I)
  #:contract (rc-wf-c D (p ...) C)
  [------------------- wf-end
   (rc-wf-c _ () (chor))]
  [(rc-wf-c D (p_1 ...) (chor I ...))
   (side-condition (not (apply equal? (term (p q)))))
   (where (p_2 ...) ,(apply set-union (term ((p q) (p_1 ...)))))
   ------------------------------------------------------------- wf-com
   (rc-wf-c D (p_2 ...) (chor (p e → q x) I ...))]
  [(rc-wf-c D (p_1 ...) (chor I ...))
   (side-condition (not (apply equal? (term (p q)))))
   (where (p_2 ...) ,(apply set-union (term ((p q) (p_1 ...)))))
   ------------------------------------------------------------- wf-sel
   (rc-wf-c D (p_2 ...) (chor (p → q [l]) I ...))]
  [(rc-wf-c D (p_1 ...) (chor I ...))
   (where (p_2 ...) ,(apply set-union (term ((p) (p_1 ...)))))
   ----------------------------------------------------------- wf-local
   (rc-wf-c D (p_2 ...) (chor (p x := e) I ...))]
  [(rc-wf-c D (p_1 ...) C_1)
   (rc-wf-c D (p_2 ...) C_2)
   (rc-wf-c D (p_3 ...) (chor I ...))
   (where (p_4 ...)
          ,(apply set-union (term ((p) (p_1 ...) (p_2 ...) (p_3 ...)))))
   --------------------------------------------------------------------- wf-cond
   (rc-wf-c D (p_4 ...) (chor (if (p e) C_1 C_2) I ...))]
  [(where ((q ...) _) (get-def D X))
   (rc-wf-c D (p_1 ...) (chor I ...))
   (side-condition ,(= (length (term (p ...))) (length (term (q ...)))))
   (side-condition ,(not (check-duplicates (term (p ...)))))
   (where (p_2 ...) ,(apply set-union (term ((p ...) (p_1 ...)))))
   --------------------------------------------------------------------- wf-call
   (rc-wf-c D (p_2 ...) (chor (X p ...) I ...))])

(define-judgment-form RecursiveChor
  #:mode (rc-wf-d I O)
  #:contract (rc-wf-d D ((X (p ...)) ...))
  [(rc-wf-c D (p ...) C)
   ...
   (side-condition ,(andmap (compose not check-duplicates)
                            (term ((q ...) ...))))
   (side-condition ,(andmap (applify subset?) (term (((p ...) (q ...)) ...))))
   (side-condition ,(andmap (compose (partial < 1) length)
                            (term ((q ...) ...))))
   ---------------------------------------------------------------------------
   (rc-wf-d (name D (dstore (X ((q ...) C)) ...)) ((X (p ...)) ...))])

(define-judgment-form RecursiveChor
  #:mode (rc-wf-f I O)
  #:contract (rc-wf-f Conf (p ...))
  [(rc-wf-c D (p ...) C)
   (rc-wf-d D _)
   ------------------------------
   (rc-wf-f (conf C _ D) (p ...))])

;; (judgment-holds (rc-wf-c D-ping any C-ping) any)
;; (judgment-holds (rc-wf-d D-ping any) any)
;; (judgment-holds (rc-wf-d (dstore (X ((p) (chor (p x := e))))) any) any)
;; (judgment-holds (rc-wf-f (conf C-ping (cstore) D-ping) any) any)
