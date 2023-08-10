#lang racket

(require "GeneralUtils.rkt")
(require "EvaluationStructs.rkt")
(require "EvaluationUtils.rkt")
(require "MatchingUtils.rkt")
(require "Desugar.rkt")
(require "ErrorHandling.rkt")

; p : environment?
; e : expression?
(define (val ρ e)
  (match e

    [`(the ,type ,expr) (val ρ expr)]
    [`(match ,type-in ,type-out ,expr ,case0 ,case* ...)
     (do-match ρ type-in type-out (val ρ expr) case0 case*)]
    [`(U ,lvl) (UNI (val ρ lvl))]
    [`(,(or 'Π 'Pi) ((,x ,A)) ,B)
     (PI (val ρ A) (CLOS ρ x B))]

    [`(,(or 'λ 'lambda) (,x) ,b)
     (LAM (CLOS ρ x b))]
    [`(Σ ((,x ,A)) ,D)
     (SIGMA (val ρ A) (CLOS ρ x D))]
    [`(cons ,a ,d)
     (PAIR (val ρ a) (val ρ d))]

    [`(List ,E) (LIST (val ρ E))]

    [`(:: ,head ,tail) (CONCAT:: (val ρ head) (val ρ tail))]

    ['nil (NIL)]

    [`(Vec ,E ,n) (VEC (val ρ E) (val ρ n))]
    [`(vec:: ,head ,tail) (VCAT:: (val ρ head) (val ρ tail))]
    ['vecnil (VECNIL)]
    [`(car ,pr)
     (do-car (val ρ pr))]
    [`(cdr ,pr)
     (do-cdr (val ρ pr))]
    ['Nat (NAT)]
    ['zero (ZERO)]
    ['infty (INFTY)]
    [`(add1 ,n) (ADD1 (val ρ n))]
    [`(+ ,x ,y) (do-+ (val ρ x) (val ρ y))]
    [`(ind-Nat ,target ,motive ,base ,step)
     (do-ind-Nat (val ρ target) (val ρ motive) (val ρ base) (val ρ step))]

    [`(ind-List ,target ,motive ,base, step)
     (do-ind-List (val ρ target) (val ρ motive) (val ρ base) (val ρ step))]

    [`(ind-Vec ,n ,target ,motive ,base, step)
     (do-ind-Vec (val ρ n) (val ρ target) (val ρ motive) (val ρ base) (val ρ step))]
    [`(= ,A ,from ,to)
     (EQ (val ρ A) (val ρ from) (val ρ to))]
    ['same
     (SAME)]

    [`(replace ,target ,motive ,base)
     
     (do-replace (val ρ target) (val ρ motive) (val ρ base))]
    ['Trivial (TRIVIAL)]
    ['sole (SOLE)]
    ['Absurd (ABSURD)]
    [`(ind-Absurd ,target ,motive) (do-ind-Absurd (val ρ target) (val ρ motive))]
    ['Atom (ATOM)]
    [`',a  (QUOTE a)]
    [`(,rator ,rand)
     (do-ap (val ρ rator) (val ρ rand))]
    [x #:when (var? x)
       (if (string-prefix? (symbol->string x) "rec-")
           (match (cdr (assv x ρ))
             [(LAM (CLOS p n b))
              (LAM (CLOS (cons (assv x ρ) p) n b))])
           (cdr (assv x ρ)))]))

; c : closure?
; v : value?
(define (val-of-closure c v)
  (match c
    [(CLOS ρ x e) (val (extend ρ x v) e)]
    [(H-O-CLOS x f) (f v)]))

; Γ : context?
; norm : norm?

(define (read-back-norm Γ norm)
  (match norm
    [(THE (NAT) (ZERO)) 'zero]
    [(THE (NAT) (INFTY)) 'infty]
    [(THE (NAT) (ADD1 n))
     `(add1 ,(read-back-norm Γ (THE (NAT) n)))]

    [(THE (LIST E) (NIL)) 'nil]

    [(THE (LIST E) (CONCAT:: hed tal)) `(:: ,(read-back-norm Γ (THE E hed)) ,(read-back-norm Γ (THE (LIST E) tal)))]

    [(THE (VEC E n) (VECNIL)) 'vecnil]

    [(THE (VEC E (ADD1 n)) (VCAT:: hed tal)) `(vec:: ,(read-back-norm Γ (THE E hed)) ,(read-back-norm Γ (THE (VEC E n) tal)))]
    [(THE (PI A B) f)
     (define x (closure-name B))
     (define y (freshen (map car Γ) x))

     (define y-val (NEU A (N-var y)))
     `(λ (,y)
        ,(read-back-norm (extend-ctx Γ y A)
                         (THE (val-of-closure B y-val)
                              (do-ap f y-val))))]
    [(THE (SIGMA A D) p)
     (define the-car (THE A (do-car p)))
     (define the-cdr (THE (val-of-closure D the-car) (do-cdr p)))
     `(cons ,(read-back-norm Γ the-car) ,(read-back-norm Γ the-cdr))]
    [(THE (TRIVIAL) _) 'sole]
    [(THE (ABSURD) (NEU (ABSURD) ne))
     `(the Absurd
           ,(read-back-neutral Γ ne))]
    [(THE (EQ A from to) (SAME)) 'same]
    [(THE (ATOM) (QUOTE x)) `',x]

    [(THE (UNI n) (LIST E)) `(List ,(read-back-norm Γ (THE (UNI n) E)))]

    [(THE (UNI n) (VEC E s)) `(Vec ,(read-back-norm Γ (THE (UNI n) E)) ,(read-back-norm Γ (THE (NAT) s)))]
    [(THE (UNI n) (NAT)) 'Nat]
    [(THE (UNI n) (ATOM)) 'Atom]
    [(THE (UNI n) (TRIVIAL)) 'Trivial]
    [(THE (UNI n) (ABSURD)) 'Absurd]
    [(THE (UNI n) (EQ A from to))
     `(= ,(read-back-norm Γ (THE (UNI n) A))
         ,(read-back-norm Γ (THE A from))
         ,(read-back-norm Γ (THE A to)))]

    [(THE (UNI n) (SIGMA A D))
     (define x (closure-name D))
     (define y (freshen (map car Γ) x))
     `(Σ ((,y ,(read-back-norm Γ (THE (UNI n) A))))
         ,(read-back-norm (extend-ctx Γ y A)
                          (THE (UNI n) (val-of-closure D (NEU A (N-var y))))))]
    [(THE (UNI n) (PI A B))
     (define x (closure-name B))
     (define y (freshen (map car Γ) x))
     `(Π ((,y ,(read-back-norm Γ (THE (UNI n) A))))
         ,(read-back-norm (extend-ctx Γ y A)
                          (THE (UNI n) (val-of-closure B (NEU A (N-var y))))))]

    [(THE (UNI k) (UNI n)) `(U ,(read-back-norm Γ (THE (NAT) n)))]
    [(THE t1 (NEU t2 ne))
     (read-back-neutral Γ ne)]))

; Γ : context?
; neu : neutral?

(define (read-back-neutral Γ neu)
  (match neu
    [(N-var x) x]
    [(N-ap ne rand)
     `(,(read-back-neutral Γ ne)
       ,(read-back-norm Γ rand))]
    [(N-car ne) `(car ,(read-back-neutral Γ ne))]
    [(N-cdr ne) `(cdr ,(read-back-neutral Γ ne))]
    [(N-ind-Nat ne motive base step)
     `(ind-Nat ,(read-back-neutral Γ ne)
               ,(read-back-norm Γ motive)
               ,(read-back-norm Γ base)
               ,(read-back-norm Γ step))]

    [(N-ind-List ne motive base step)
     `(ind-List ,(read-back-neutral Γ ne)
               ,(read-back-norm Γ motive)
               ,(read-back-norm Γ base)
               ,(read-back-norm Γ step))]

    [(N-ind-Vec n ne motive base step)
     `(ind-Vec ,(read-back-neutral Γ n)
               ,(read-back-neutral Γ ne)
               ,(read-back-norm Γ motive)
               ,(read-back-norm Γ base)
               ,(read-back-norm Γ step))]
    

    [(N-+ x y)
     `(+ ,(read-back-neutral Γ x) ,(read-back-neutral Γ y))]
    [(N-match type-in type-out expr case0 case*)
     (append `(match ,type-in ,type-out ,(read-back-neutral Γ expr)) (cons case0 case*))]

    [(N-replace ne motive base)
     `(replace ,(read-back-neutral Γ ne)
               ,(read-back-norm Γ motive)
               ,(read-back-norm Γ base))]
    [(N-ind-Absurd ne motive)
     `(ind-Absurd (the Absurd ,(read-back-neutral Γ ne))
                  ,(read-back-norm Γ motive))]))

; v : value?
(define (do-car v)
  (match v
    [(PAIR a d) a]
    [(NEU (SIGMA A _) ne)
     (NEU A (N-car ne))]))

; v : value?
(define (do-cdr v)
  (match v
    [(PAIR a d) d]
    [(NEU (SIGMA _ D) ne)
     (NEU (val-of-closure D (do-car v))
          (N-cdr ne))]))

; fun : value?
; arg : value?

(define (do-ap fun arg)
  (match fun
    [(LAM c)
     (val-of-closure c arg)]
    [(NEU (PI A B) ne)
     (NEU (val-of-closure B arg)
          (N-ap ne (THE A arg)))]))

; target : value?
; motive : value?

(define (do-ind-Absurd target motive)
  (match target
    [(NEU (ABSURD) ne)
     (NEU motive (N-ind-Absurd ne (THE (UNI (ZERO)) motive)))]))

; target : value?
; motive : value?
; base : value?



(define (do-replace target motive base)
  (match target
    [(SAME) base]
    [(NEU (EQ A from to) ne)
     (NEU (do-ap motive to)
          (N-replace ne
                     (THE (PI A (H-O-CLOS 'x (lambda (_) (UNI (ZERO)))))
                          motive)
                     (THE (do-ap motive from)
                          base)))]))

(define (do-+ x y)
  (cond
    [(and (NEU? x) (NEU? y)) (NEU (NAT) (N-+ (match x [(NEU (NAT) ne) ne]) (match y [(NEU (NAT) ne) ne])))]
    [(NEU? x) (create-add1s (count-add1s y) x)]
    [(NEU? y) (create-add1s (count-add1s x) y)]
    [else (create-add1s (+ (count-add1s x) (count-add1s y)) (ZERO))]))

; target : value?
; motive : value?
; base : value?
; step : value?

(define (do-ind-Nat target motive base step)
  (match target
    [(ZERO) base]
    [(ADD1 n) (do-ap (do-ap step n) (do-ind-Nat n motive base step))]
    [(NEU (NAT) ne)
     (NEU (do-ap motive target)
          (N-ind-Nat
           ne
           (THE (PI (NAT)
                    (H-O-CLOS 'k (lambda (k) (UNI (INFTY)))))
                motive)
           (THE (do-ap motive (ZERO)) base)
           (THE (ind-Nat-step-type motive)
                step)))]))

; motive : value?
(define (ind-Nat-step-type motive)
  (PI (NAT)
      (H-O-CLOS 'n-1
                (lambda (n-1)
                  (PI (do-ap motive n-1)
                      (H-O-CLOS 'ih
                                (lambda (ih)
                                  (do-ap motive (ADD1 n-1)))))))))

(define (do-ind-List target motive base step)
  (match target
    [(NIL) base]
    [(CONCAT:: hed res) (do-ap (do-ap (do-ap step hed) res) (do-ind-List res motive base step))]
    [(NEU (LIST E) ne)
     (NEU (do-ap motive target)
          (N-ind-List
           ne
           (THE (PI (LIST E)
                    (H-O-CLOS 'k (lambda (k) (UNI (INFTY)))))
                motive)
           (THE (do-ap motive (NIL)) base)
           (THE (ind-List-step-type motive E)
                step)))]))
(define (ind-List-step-type motive E)
  (PI E
      (H-O-CLOS 'hed
                (lambda (hed)
                  (PI (LIST E)
                      (H-O-CLOS 'tal
                                (lambda (tal)
                                  (PI (do-ap motive tal)
                                      (H-O-CLOS 'ih
                                                (lambda (ih)
                                                  (do-ap motive (CONCAT:: hed tal))))))))))))


(define (do-ind-Vec n target motive base step)
  (match target
    [(VECNIL) base]
    [(VCAT:: hed res) (match n [(ADD1 t) (do-ap (do-ap (do-ap (do-ap step t) hed) res) (do-ind-Vec t res motive base step))])]
    [(NEU (VEC E k) ne)
     (NEU ((do-ap motive n) target)
          (N-ind-Vec
           n
           ne
           (THE (PI (NAT) (H-O-CLOS 'arg (lambda (arg) (PI (LIST E)
                    (H-O-CLOS 'k (lambda (k) (UNI (INFTY))))))))
                motive)
           (THE (do-ap (do-ap motive (ZERO)) (VECNIL)) base)
           (THE (ind-Vec-step-type motive E)
                step)))]))

(define (ind-Vec-step-type motive E)
  (PI (NAT) (H-O-CLOS 'arg (lambda (arg)
      (PI E
      (H-O-CLOS 'hed
                (lambda (hed)
                  (PI (VEC E arg)
                      (H-O-CLOS 'tal
                                (lambda (tal)
                                  (PI (do-ap (do-ap motive arg) tal)
                                      (H-O-CLOS 'ih
                                                (lambda (ih)
                                                  (do-ap (do-ap motive (ADD1 arg)) (VCAT:: hed tal)))))))))))))))

(define (do-match ρ type-in type-out expr case0 case*)
  (if (NEU? expr)
      (NEU (val ρ type-out) (N-match type-in type-out (match expr [(NEU X ne) ne]) case0 case*))
      (let* ([expr-norm (read-back-norm ρ (THE (val ρ type-in) expr))]
             [case-out (match-cases expr-norm case0 case*)]
             [r-out (replace-arbitraries expr-norm case-out)])
        (val ρ (desugar r-out)))))

; t : value?
; v1 : value?
; v2 : value?

(define (convert Γ t v1 v2)
  (define e1 (read-back-norm Γ (THE t v1)))
  (define e2 (read-back-norm Γ (THE t v2)))
  (if (α-equiv? e1 e2)
      (go 'ok)
      (stop e1 (format "Expected to be the same ~v as ~v"
                       (read-back-norm Γ (THE (match t [(UNI n) (UNI (ADD1 n))]) t))
                       e2))))

(provide (all-defined-out))