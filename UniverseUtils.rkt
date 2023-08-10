#lang racket
(require "Evaluation.rkt")
(require "EvaluationStructs.rkt")
(require "GeneralUtils.rkt")
(require "ErrorHandling.rkt")

(define (α-subtype-aux e1 e2 xs1 xs2)
  (match* (e1 e2)
    [(`(U ,n1) `(U infty)) #t]
    [(`(U (add1 ,n1)) `(U (add1 ,n2))) (α-subtype-aux `(U ,n1) `(U ,n2) xs1 xs2)]
    [(`(U ,n1) `(U (add1,n2))) (α-subtype-aux `(U ,n1) `(U ,n2) xs1 xs2)]
    [(`(U (add1 ,n1)) `(U ,n2)) #f]
    [(`(U ,n1) `(U ,n2)) (α-equiv-aux n1 n2 xs1 xs2)]
    [(kw kw)
     #:when (keyword? kw)
     #t]
    [(x y)
     #:when (and (var? x) (var? y))
     (match* ((assv x xs1) (assv y xs2))
       [(#f #f) (eqv? x y)]
       [((cons _ b1) (cons _ b2)) (eqv? b1 b2)]
       [(_ _) #f])]
    [(`(Π ((,x ,A1)) ,B1) `(Π ((,y ,A2)) ,B2))
     (and (α-subtype-aux A1 A2 xs1 xs2)
          (let ([fresh (gensym)])
            (let ([bigger1 (cons (cons x fresh) xs1)]
                  [bigger2 (cons (cons y fresh) xs2)])
              (α-subtype-aux B1 B2 bigger1 bigger2))))]
    [(`(Σ ((,x ,A1)) ,B1) `(Σ ((,y ,A2)) ,B2))
     (and (α-subtype-aux A1 A2 xs1 xs2)
          (let ([fresh (gensym)])
            (let ([bigger1 (cons (cons x fresh) xs1)]
                  [bigger2 (cons (cons y fresh) xs2)])
              (α-subtype-aux B1 B2 bigger1 bigger2))))]
    [(`',x  `',y)
     (eqv? x y)]

    [(`(the Absurd ,e1) `(the Absurd ,e2))
     #t]
    [((cons op args1) (cons op args2))
     #:when (keyword? op)
     (and (= (length args1) (length args2))
          (for/and ([arg1 (in-list args1)]
                    [arg2 (in-list args2)])
            (α-subtype-aux arg1 arg2 xs1 xs2)))]
    [((list rator1 rand1) (list rator2 rand2))
     (and (α-subtype-aux rator1 rator2 xs1 xs2)
          (α-subtype-aux rand1 rand2 xs1 xs2))]
    [(_ _) #f]))

(define (subtype? e1 e2)
  (α-subtype-aux e1 e2 '() '()))

(define (subtype-convert Γ lvl t1 t2)
  (define e1 (read-back-norm Γ (THE (UNI (ZERO)) t1)))
  (define e2 (read-back-norm Γ (THE (UNI (ZERO)) t2)))
  (if (subtype? e1 e2)
      (go 'ok)
      (stop e1 (format "Expected to be the same ~v as ~v"
                       `(add1 ,lvl)
                       e2))))

(define (greater-Nat A B)
  (match* (A B)
    [(`(add1 ,n ) `(add1 ,k ))  `(add1 ,(greater-Nat k n))]
    [(`zero `(add1 ,k)) `(add1 ,k)]
    [(`(add1 ,k) `zero) `(add1 ,k)]
    [(`zero `zero) `zero]
    [(k `(add1 ,k)) `(add1 ,k)]
    [(`(add1 ,k) k) `(add1 ,k)]
    [(k k) k]
    [(`zero k) k]
    [(k `zero) k]
    [(`infty k) `infty]
    [(k `infty) `infty]
    [(k `(add1 ,t)) `(add1 ,(greater-Nat k t)) ]
    [(`(add1 ,t) k) `(add1 ,(greater-Nat k t)) ]
    ))

(provide subtype-convert greater-Nat)