#lang racket

(require racket/set)
(require racket/date)
(require redex)

;; TODO: Add tags. (pstore ...), (cstore ...), (chor ...), (inst ...), etc.?

;; TODO: Think about whether variable-not-otherwise-mentioned is actually
;; necessary for e.g. labels.

;; TODO: Proper tests.

;; NOTE: Prefer judgment forms over metafunctions? Neither are easily extensible
;; though...

;;; Util

(define (aput k v alist #:equal? [equal? equal?] #:less? [less? symbol<?])
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

(define (assoc-second k alist)
  (let ([v (assoc k alist)])
    (if v (second v) '())))

;;; SimpleChor

(define-language SimpleChor
  (id ::= variable-not-otherwise-mentioned)
  (p q ::= id)
  (I ::= (com p q))
  (C ::= (I ...)))

(define-metafunction SimpleChor
  pn-0-inst : I -> (p ...)
  [(pn-0-inst (com p q)) (p q)])

(define-metafunction SimpleChor
  pn-0 : C -> (p ...)
  [(pn-0 C) ,(remove-duplicates
            (append-map (lambda (i) (term (pn-0-inst ,i))) (term C)))])

(define-metafunction SimpleChor
  pn-0-disjoint? : C C -> boolean
  [(pn-0-disjoint? C_1 C_2)
   ,(set-disjoint? (term (pn-0 C_1)) (term (pn-0 C_2)))])

;; (redex-match SimpleChor C (term ((com p q) (com a b))))
;; (term (pn-0 ((com p q) (com a b) (com p q))))

(define SimpleChor->
  (reduction-relation
   SimpleChor
   #:domain C
   (--> ((com p q) I ...)
        (I ...)
        com)
   (--> (I_1 I_2 ... I I_3 ...)
        (I_1 I_2 ... I_3 ...)
        (side-condition (term (pn-0-disjoint? (I_1 I_2 ...) (I))))
        delay)))

;; (apply-reduction-relation SimpleChor-> (term ((com p q) (com p r))))
;; (traces SimpleChor-> (term ((com p q) (com p r))))
;; (traces SimpleChor-> (term ((com p q) (com r q))))
;; (traces SimpleChor-> (term ((com p q) (com r s))))

;;; StatefulChor

(define-extended-language StatefulChor SimpleChor
  ;; Expressions
  (v ::= boolean natural string)
  (x ::= id)
  (f ::= id)
  (e ::= v x (f e ...))
  (E ::= hole (f v ... E e ...))
  ;; Stores
  (σ ::= ((x v) ...))
  (Σ ::= ((p σ) ...))
  ;; Choreographies
  (I ::=
     (com (p e) (q x))
     (:= p x e))
  ;; Configurations
  (Conf ::= (C Σ)))

(define-metafunction StatefulChor
  assoc-var : σ x -> (boolean v)
  [(assoc-var σ x)
   (#t v)
   (where v ,(assoc-second (term x) (term σ)))]
  [(assoc-var σ x) (#f #f)])

(define-metafunction StatefulChor
  assoc-store : Σ p -> σ
  [(assoc-store Σ p) ,(assoc-second (term p) (term Σ))])

(define-metafunction StatefulChor
  aput-var : Σ p x v -> Σ
  [(aput-var Σ p x v)
   ,(aput (term p) (list (aput (term x) (list (term v)) (term σ))) (term Σ))
   (where σ (assoc-store Σ p))])

(define-metafunction StatefulChor
  pn-1-inst : I -> (p ...)
  [(pn-1-inst (com (p e) (q x))) (p q)]
  [(pn-1-inst (:= p x e)) (p)])

(define-metafunction StatefulChor
  pn-1 : C -> (p ...)
  [(pn-1 C) ,(remove-duplicates
              (append-map (lambda (i) (term (pn-1-inst ,i))) (term C)))])

(define-metafunction StatefulChor
  pn-1-disjoint? : C C -> boolean
  [(pn-1-disjoint? C_1 C_2)
   ,(set-disjoint? (term (pn-1 C_1)) (term (pn-1 C_2)))])

(define StatefulChorExpr->
  (reduction-relation
   StatefulChor
   #:domain (e σ)
   (--> ((in-hole E x) (name σ ((x_1 v_1) ... (x v) (x_2 v_2) ...)))
        ((in-hole E v) σ)
        var)
   (--> ((in-hole E (f v ...)) σ)
        ((in-hole E ,(apply (eval (term f)) (term (v ...)))) σ)
        call)))

;; (traces StatefulChorExpr-> (term ((+ (+ (+ a b) 1) c) ((a 1) (b 2) (c 3)))))
;; (traces StatefulChorExpr-> (term ((string-append "hello" "world") ())))

(define-judgment-form StatefulChor
  #:mode (↓ I I O)
  #:contract (↓ σ e v)
  [---- val
   (↓ _ v v)]
  [(where (#t v) (assoc-var σ x))
   ---- var
   (↓ σ x v)]
  [(↓ σ e v)
   ...
   ---- call
   (↓ σ (f e ...) ,(apply (eval (term f)) (term (v ...))))])

;; (judgment-holds (↓ ((a 2) (b 3)) (+ 2 5 a b) v) v)
;; (show-derivations (build-derivations (↓ ((a 2) (b 3)) (+ 2 5 a b) v)))

;; NOTE: If a process doesn't yet possess a referenced variable, the judgment
;; should just not hold, instead of throwing an error.

;; (judgment-holds (↓ (assoc-store ((p ())) p) x v) v)

(define StatefulChor->
  (reduction-relation
   StatefulChor
   #:domain Conf
   (--> (((:= p x e) I ...) Σ)
        ((I ...) (aput-var Σ p x v))
        (judgment-holds (↓ (assoc-store Σ p) e v))
        local)
   (--> (((com (p e) (q x)) I ...) Σ)
        ((I ...) (aput-var Σ q x v))
        (judgment-holds (↓ (assoc-store Σ p) e v))
        com)
   ;; TODO: This never actually "executes" the instruction I, in the sense that
   ;; it never applies the store updates that rules `local` and `com` would
   ;; have.
   (--> ((I_1 I_2 ... I I_3 ...) Σ)
        ((I_1 I_2 ... I_3 ...) Σ)
        (side-condition (term (pn-1-disjoint? (I_1 I_2 ...) (I))))
        delay)))

(define (catalogue title)
  (case title
    [("My Choreographies") 100]
    [else (error 'catalogue "no book named ~s" title)]))

;; (traces StatefulChor-> (term (((com (Buyer title) (Seller x))
;;                                (com (Seller (catalogue x)) (Buyer price)))
;;                               ((Buyer ((title "My Choreographies")))))))

;; (traces StatefulChor-> (term (((com (p 5) (q x))
;;                                (:= r y 4))
;;                               ())))

(define StatefulChor->2
  (reduction-relation
   StatefulChor
   #:domain Conf
   (--> ((I_1 ... (name I (:= p x e)) I_2 ...) Σ)
        ((I_1 ... I_2 ...) (aput-var Σ p x v))
        (side-condition (term (pn-1-disjoint? (I_1 ...) (I))))
        (judgment-holds (↓ (assoc-store Σ p) e v))
        (computed-name (format "τ@~a" (term p))))
   (--> ((I_1 ... (name I (com (p e) (q x))) I_2 ...) Σ)
        ((I_1 ... I_2 ...) (aput-var Σ q x v))
        (side-condition (term (pn-1-disjoint? (I_1 ...) (I))))
        (judgment-holds (↓ (assoc-store Σ p) e v))
        (computed-name (format "~a.~s -> ~a.~a"
                               (term p) (term v) (term q) (term x))))))

;; (traces StatefulChor->2 (term (((com (Buyer title) (Seller x))
;;                                 (com (Seller (catalogue x)) (Buyer price)))
;;                                ((Buyer ((title "My Choreographies")))))))

;; (traces StatefulChor->2 (term (((com (p 5) (q x))
;;                                 (:= r y 4))
;;                                ())))

(define-judgment-form StatefulChor
  #:mode (→ I O O)
  #:contract (→ Conf ((p ...) string) Conf)
  [(↓ (assoc-store Σ p) e v)
   ---- local
   (→ (((:= p x e) I ...) Σ)
      ((p) ,(format "τ@~a" (term p)))
      ((I ...) (aput-var Σ p x v)))]
  [(↓ (assoc-store Σ p) e v)
   ---- com
   (→ (((com (p e) (q x)) I ...) Σ)
      ((p q) ,(format "~a.~v -> ~a.~a" (term p) (term v) (term q) (term x)))
      ((I ...) (aput-var Σ q x v)))]
  [(→ ((I_1 ...) Σ_1)
      (name μ ((p ...) _))
      ((I_2 ...) Σ_2))
   (side-condition ,(set-disjoint? (term (pn-1 (I))) (term (p ...))))
   ---- delay
   (→ ((I I_1 ...) Σ_1)
      μ
      ((I I_2 ...) Σ_2))])

;; (judgment-holds (→ (((com (Buyer title) (Seller x)))
;;                     ((Buyer ((title "My Choreographies")))))
;;                    (name μ any)
;;                    (C Σ))
;;                 (C Σ μ))

;; (judgment-holds (→ (((com (Seller (catalogue x)) (Buyer price)))
;;                     ((Buyer ((title "My Choreographies")))
;;                      (Seller ((x "My Choreographies")))))
;;                    (name μ any)
;;                    (C Σ))
;;                 (C Σ μ))

;; (judgment-holds (→ (((com (Buyer title) (Seller x))
;;                      (com (Seller (catalogue x)) (Buyer price)))
;;                     ((Buyer ((title "My Choreographies")))))
;;                    (name μ any)
;;                    (C Σ))
;;                 (C Σ μ))

(define StatefulChor->3
  (reduction-relation
   StatefulChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (→ Conf_1 (_ string) Conf_2))
        (computed-name (term string)))))

;; (traces StatefulChor->3 (term (((com (Buyer title) (Seller x))
;;                                 (com (Seller (catalogue x)) (Buyer price)))
;;                                ((Buyer ((title "My Choreographies")))))))

;; (traces StatefulChor->3 (term (((com (p 5) (q x))
;;                                 (:= r y 4))
;;                                ())))

;;; ConditionalChor

(define-extended-language ConditionalChor StatefulChor
  ;; Choreographies
  (I ::=
     (com (p e) (q x))
     (:= p x e)
     (if (p e) C_1 C_2)))

(define-metafunction ConditionalChor
  pn-2-inst : I -> (p ...)
  [(pn-2-inst (com (p e) (q x))) (p q)]
  [(pn-2-inst (:= p x e)) (p)]
  [(pn-2-inst (if (p e) (I_1 ...) (I_2 ...)))
   ,(cons (term p)
          (apply append (term ((pn-2-inst I_1) ... (pn-2-inst I_2) ...))))])

(define-metafunction ConditionalChor
  pn-2 : C -> (p ...)
  [(pn-2 (I ...))
   ,(remove-duplicates (apply append (term ((pn-2-inst I) ...))))])

(define-overriding-judgment-form ConditionalChor →
  #:mode (→2 I O O)
  #:contract (→2 Conf ((p ...) string) Conf)
  [(↓ (assoc-store Σ p) e #t)
   ---- cond-then
   (→2 (((if (p e) (I_1 ...) C_2) I ...) Σ)
       ((p) ,(format "τ@~a" (term p)))
       ((I_1 ... I ...) Σ))]
  [(↓ (assoc-store Σ p) e #f)
   ---- cond-else
   (→2 (((if (p e) C_1 (I_2 ...)) I ...) Σ)
       ((p) ,(format "τ@~a" (term p)))
       ((I_2 ... I ...) Σ))]
  [(→2 ((I_1 ...) Σ_1)
       (name μ ((p ...) _))
       ((I_2 ...) Σ_2))
   (side-condition ,(set-disjoint? (term (pn-2 (I))) (term (p ...))))
   ---- delay
   (→2 ((I I_1 ...) Σ_1)
       μ
       ((I I_2 ...) Σ_2))]
  [(→2 (C_1 Σ_1) (name μ ((p ...) _)) (C_2 Σ_2))
   (→2 (C_3 Σ_1) (name μ ((p ...) _)) (C_4 Σ_2))
   (side-condition ,(set-disjoint? (term (q)) (term (p ...))))
   ---- delay-cond
   (→2 (((if (q e) C_1 C_3) I ...) Σ_1)
       μ
       (((if (q e) C_2 C_4) I ...) Σ_2))])

(define-term C6-2
  ((if (p (< x 10))
       ((:= q y #t) (:= p x (+ x 1)))
       ((:= q y #t)))))

(define-term Σ6-2
  ((p ((x 5)))
   (q ((y #t)))))

;; (judgment-holds (→2 (C6-2 Σ6-2) (name μ any) (C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (→2 (C6-2 Σ6-2) (name μ any) (C Σ))))

(define ConditionalChor->
  (reduction-relation
   ConditionalChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (→2 Conf_1 (_ string) Conf_2))
        (computed-name (term string)))))

;; (traces ConditionalChor-> (term (C6-2 Σ6-2)))

;;; SelectiveChor

(define-extended-language SelectiveChor ConditionalChor
  ;; Labels
  (l ::= id)
  ;; Choreographies
  (I ::=
     (com (p e) (q x))
     (sel p q l)
     (:= p x e)
     (if (p e) C_1 C_2)))

(define-metafunction SelectiveChor
  pn-3-inst : I -> (p ...)
  [(pn-3-inst (com (p e) (q x))) (p q)]
  [(pn-3-inst (sel p q l)) (p q)]
  [(pn-3-inst (:= p x e)) (p)]
  [(pn-3-inst (if (p e) (I_1 ...) (I_2 ...)))
   ,(cons (term p)
          (apply append (term ((pn-3-inst I_1) ... (pn-3-inst I_2) ...))))])

(define-metafunction SelectiveChor
  pn-3 : C -> (p ...)
  [(pn-3 (I ...))
   ,(remove-duplicates (apply append (term ((pn-3-inst I) ...))))])

(define-overriding-judgment-form SelectiveChor →2
  #:mode (→3 I O O)
  #:contract (→3 Conf ((p ...) string) Conf)
  [---- sel
   (→3 (((sel p q l) I ...) Σ)
       ((p q) ,(format "~a -> ~a[~a]" (term p) (term q) (term l)))
       ((I ...) Σ))]
  [(→3 ((I_1 ...) Σ_1)
       (name μ ((p ...) _))
       ((I_2 ...) Σ_2))
   (side-condition ,(set-disjoint? (term (pn-3 (I))) (term (p ...))))
   ---- delay
   (→3 ((I I_1 ...) Σ_1)
       μ
       ((I I_2 ...) Σ_2))])

(define (timestamp)
  (date->string (current-date)))

(define-term C6-16
  ((com (Buyer title) (Seller x))
   (com (Seller (catalogue x)) (Buyer price))
   (if (Buyer (< price 150))
       ((sel Buyer Seller ok)
        (com (Buyer address) (Seller y))
        (com (Seller (format "~a: ~a" y (timestamp))) (Buyer date)))
       ((sel Buyer Seller ko)))))

(define-term Σ6-16
  ((Buyer ((title "My Choreographies")
           (address "Internet Street")))))

;; (judgment-holds (→3 (C6-16 Σ6-16) (name μ any) (C Σ)) (C Σ μ))
;; (show-derivations (build-derivations (→3 (C6-16 Σ6-16) (name μ any) (C Σ))))

(define SelectiveChor->
  (reduction-relation
   SelectiveChor
   #:domain Conf
   (--> Conf_1 Conf_2
        (judgment-holds (→3 Conf_1 (_ string) Conf_2))
        (computed-name (term string)))))

;; (traces SelectiveChor-> (term (C6-16 Σ6-16)))

;;; TODO: RecursiveChor

;;; TODO: Chapter 10

;;; TODO: Typing
