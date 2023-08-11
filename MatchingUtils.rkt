#lang racket

(require "ErrorHandling.rkt")
(require "GeneralUtils.rkt")
(require "EvaluationStructs.rkt")

(define a-matchables
  (list 'zero 'Nat 'Atom 'List 'Vec 'nil 'vecnil 'U))



(define (a-matchable? x)
  (if (or (or (memv x a-matchables) (list? x)) (arbitrary? x))
      #t
      #f))


(define (replace-arbitraries expr case)
  (match case
    [`(,m ,r) (replace-arbitraries-expr (arbitrary-to-expr expr m) r)]))


(define (replace-arbitraries-expr a-to-e r)
  (cond
    [(arbitrary? r) (match (cdr (assv r a-to-e)) [`(,e) e])]
    [(b-list? r) (replace-arbitraries-list a-to-e r)]
    [else r]))

(define (replace-arbitraries-list a-to-e r)
  (match r
    [`(,r0 ,rs ...)
     (append (list (replace-arbitraries-expr a-to-e r0)) (replace-arbitraries-list a-to-e rs))]
    [`() `()]))

(define (arbitrary-to-expr expr m)
  (cond
    [(arbitrary? m) `(,(list m expr))]
    [(b-list? m) (list-arbitrary-to-expr expr m)]
    [else `()]))

(define (list-arbitrary-to-expr expr m)
  (match m
    [`(,m0 ,m* ...)
     (match expr [`(,e0 ,e* ...)
                  (append (arbitrary-to-expr e0 m0) (list-arbitrary-to-expr e* m*))])]
    [`() `()]))

(define (match-cases expr case0 case*)
   (match case0
    [`(,m ,r)
     (if (match-exprs expr m) case0 (match case*
                                   [`() #f]
                                   [`(,case1 ,case** ...) (match-cases expr case1 case**)]))]))

(define (match-exprs e m)
  (cond
    [(and (b-list? e) (b-list? m)) (match-lists e m)]
    [(and (a-matchable? e) (arbitrary? m)) #t]
    [else (equal? e m)]))
    
(define (arbitrary? e)
  (and
   (not (or (keyword? e) (list? e)))
    (string-prefix? (symbol->string e) "!")))



(define (match-lists L0 L1)
  (if (not (= (list-length L0) (list-length L1)))
      #f
      (match L0
        [`(,x ,x* ...)
         (match L1
           [`(,y ,y* ...)
            (and (match-exprs x y) (match-lists x* y*))])]
        [`() #t])))

(define (list-length L)
  (match L
    [`(,e ,es ...) (+ 1 (list-length es))]
    [`() 0]))



(define (valid-binding m r m-a r-a)
  (if (empty? r-a) (go #t)
      (cond
        [(not (subset? (list->set r-a) (list->set m-a)))
         (stop r "Arbitraries must be a subset of the arbitraries in the match check.")]
        [(not (match m
                [`(add1 ,n) #t]
                [n #t]))
         (stop m "You cannot bind variables from this match-check.")]
        [else (go #t)])))


      
(define (extend-ctx-arbitraries-to-fresh Γ m arbitraries-to-fresh type-in)
  (match arbitraries-to-fresh
    [`() Γ]
    [`(,a-to-f0 ,a-to-f* ...)
     (match a-to-f0
       [`(,a ,f) (extend-ctx
                  (extend-ctx-arbitraries-to-fresh Γ m a-to-f* type-in) f
                  (get-type-a m a type-in))])]))

(define (get-type-a m a type-in)
  (match m
    [`(add1 ,n) (NAT)]
    [`(:: ,e ,es) (cond
                    [(equal? a es) type-in]
                    [else (match type-in
                            [(LIST entry-type) entry-type])])]
    [`(vec:: ,e ,es) (match type-in
                       [(VEC entry-type len)
                        (cond
                          [(equal? a es) (VEC entry-type (match len
                                                           [(ADD1 n) n]
                                                           [n n]))]
                          [else entry-type])])]
    [`(U ,n) (NAT)]
    [`(Either ,left ,right) (match type-in
                              [(EITHER tLeft tRight)
                               (cond
                                 [(equal? a left) tLeft]
                                 [(equal? a right) tRight]
                                 [else "NEver happend1!."])])]
    [n type-in]))

(define (arbitraries-to-fresh arbitraries Γ)
  (map (lambda (a)
         `(,a ,(freshen (map car Γ) a))) (remove-duplicates arbitraries)))

(define (get-arbitraries m)
     (cond
       [(arbitrary? m) `(,m)]
       [(b-list? m) (match m
                      [`(,m0 ,m* ...) (append (get-arbitraries m0) (get-arbitraries m*))]
                      [`() `()])]
       [else `()]))

(define (check-dups m L)
  (if (check-duplicates L) (stop m "No duplicate arbitraries are allowed in match checks.")
      (go L)))

(define (match-is-total cases)
   (match cases
    [`() #f]
    [`(,case0 ,case* ...)
     (match case0
       [`(,m ,r) (if (arbitrary? m) #t (match-is-total case*))])]))

(provide (all-defined-out))