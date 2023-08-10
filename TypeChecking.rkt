#lang racket

(require "ErrorHandling.rkt")
(require "EvaluationUtils.rkt")
(require "Evaluation.rkt")
(require "EvaluationStructs.rkt")
(require "UniverseUtils.rkt")
(require "Evaluation.rkt")
(require "GeneralUtils.rkt")
(require "MatchingUtils.rkt")
(require "Desugar.rkt")
(require "RecursionUtils.rkt")

(define (check Γ e t)
  (match e
    [`(cons ,a ,d)
     (match t
       [(SIGMA A D)
        (go-on ([a-out (check Γ a A)]
                [d-out (check Γ d (val-of-closure D (val (ctx->env Γ) a-out)))])
          (go `(cons ,a-out ,d-out)))]
       [non-SIGMA (stop e (format "Expected Σ, got ~v"
                                  (read-back-norm Γ (THE (UNI (ZERO)) non-SIGMA))))])]
    ['zero
     (match t
       [(NAT) (go 'zero)]
       [non-NAT (stop e (format "Expected Nat, got ~v"
                                (read-back-norm Γ (THE (UNI (ZERO)) non-NAT))))])]
    ['infty
     (match t
       [(NAT) (go 'infty)]
       [non-NAT (stop e (format "Expected Nat, got ~v"
                                (read-back-norm Γ (THE (UNI (INFTY)) non-NAT))))])]

    [`(add1 ,n)
     (match t
       [(NAT)
        (go-on ([n-out (check Γ n (NAT))])
          (go `(add1 ,n-out)))]
       [non-NAT (stop e (format "Expected Nat, got ~v" (read-back-norm Γ (THE (UNI) non-NAT))))])]

    ['nil
     (match t
       [(LIST E) (go 'nil)]
       [non-LIST (stop e (format "Expected (List E), got ~v"
                                (read-back-norm Γ (THE (UNI (ZERO)) non-LIST))))])]
    [`(:: ,hed ,tal)
     (match t
       [(LIST E)
        (go-on ([h-out (check Γ hed E)]
                [t-out (check Γ tal (LIST E))])
          (go `(:: ,h-out ,t-out)))]
       [non-LIST (stop e (format "Expected (List E), got ~v"
                                  (read-back-norm Γ (THE (UNI (ZERO)) non-LIST))))])]

    ['vecnil
     (match t
       [(VEC E (ZERO)) (go 'vecnil)]
       [non-VEC (stop e (format "Expected (Vec E zero), got ~v"
                                (read-back-norm Γ (THE (UNI (ZERO)) non-VEC))))])]
    [`(vec:: ,hed ,tal)
     (match t
       [(VEC E (ADD1 n))
        (go-on ([h-out (check Γ hed E)]
                [t-out (check Γ tal (VEC E n))])
          (go `(vec:: ,h-out ,t-out)))]
       [non-LIST (stop e (format "Expected (Vec E (add1 n)), got ~v"
                                   (read-back-norm Γ (THE (UNI (ZERO)) non-LIST))))])]

    [`(+ ,x ,y)
     (match t
       [(NAT)
        (go-on ([x-out (check Γ x (NAT))] [y-out (check Γ y (NAT))])
               (go `(+ ,x-out ,y-out)))]
       [non-NAT (stop e (format "Expected Nat, got ~v"
                                (read-back-norm Γ (THE (UNI (ZERO)) non-NAT))))])]
    ['same
     (match t
       [(EQ A from to)
        (go-on ([_ (convert Γ A from to)])
          (go 'same))]
       [non-= (stop e (format "Expected =, got ~v"
                              (read-back-norm Γ (THE (UNI (ZERO)) non-=))))])]
    ['sole
     (match t
       [(TRIVIAL)
        (go 'sole)]
       [non-Trivial (stop e (format "Expected Trivial, got ~v"
                                    (read-back-norm Γ (THE (UNI (ZERO)) non-Trivial))))])]
    [`(,(or 'λ 'lambda) (,x) ,b)
     (match t
       [(PI A B)
        (define x-val (NEU A (N-var x)))
        (go-on ([b-out (check (extend-ctx Γ x A) b (val-of-closure B x-val))])
          (go `(λ (,x) ,b-out)))]
       [non-PI (stop e (format "Expected Π, got ~v"
                               (read-back-norm Γ (THE (UNI (ZERO)) non-PI))))])]
    [`',a
     (match t
       [(ATOM)
        (go `',a)]
       [non-ATOM (stop e (format "Expected Atom, got ~v"
                                 (read-back-norm Γ (THE (UNI (ZERO)) non-ATOM))))])]
    [none-of-the-above
     (go-on ([`(the ,t-out ,e-out) (synth Γ e)]
             [`(the ,t-of-t ,temp) (synth Γ t-out)]
             [`(U ,n) (U-check Γ t-of-t)]
             [`(the ,t-of-t2 ,temp2) (synth Γ (read-back-norm Γ (THE (UNI (ZERO)) t)))]
             [`(U ,n2) (U-check Γ t-of-t2)]
             [_ (subtype-convert Γ n2 (val (ctx->env Γ) t-out) t)])
             
       (go e-out))]))

(define (U-check Γ expr)
  (match expr
    [`(U ,n) (go `(U ,n))]
    [non-U (stop expr (format "Expected (U n) got ~v" (read-back-norm Γ (val (ctx->env Γ) (synth Γ expr) non-U))))]))

(define (check-cases Γ type-in type-out cases)
  (match cases
    [`() (go #t)]
    [`(,case0 ,case* ...)
       (match case0
         [`(,m ,r) (let ([m-arbitraries (get-arbitraries m)]
                         [r-arbitraries (get-arbitraries r)])
                     (go-on ([m-arbitraries-out (check-dups m m-arbitraries)]
                             [valid-binding-out (valid-binding m r m-arbitraries r-arbitraries)]
                             [r-out
                              (check-result-type Γ m r type-in type-out m-arbitraries r-arbitraries)]
                             [case*-out (check-cases Γ type-in type-out case*)])
                            (go cases)))])]))

(define (check-result-type Γ m r type-in type-out m-a r-a)
  (if (empty? r-a)
      (check Γ r type-out)
      (let* ([a-to-f (arbitraries-to-fresh r-a Γ)]
             [extended-ctx (extend-ctx-arbitraries-to-fresh Γ m a-to-f type-in)]
             [r-out (replace-arbitraries-expr a-to-f r)])
        (check extended-ctx (desugar r-out) type-out))))
; Γ : context?
; e : expr?

(define (synth Γ e)
  (match e
    [`(the ,type ,expr)
         (go-on ([`(the ,typeoftype ,ty) (synth Γ type)]
             [`(U ,n) (U-check Γ typeoftype)]
            [e-out (check Γ expr (val (ctx->env Γ) ty))])
        (go `(the ,ty ,e-out)))]
    [`(match ,type-in ,type-out ,expr ,case0 ,case* ...)
     (go-on ([type-in-out (check Γ type-in (UNI (INFTY)))]
             [type-out-out (check Γ type-out (UNI (INFTY)))]
             [expr-out (check Γ expr (val (ctx->env Γ) type-in-out))]
             [cases-out
              (check-cases Γ (val (ctx->env Γ) type-in-out) (val (ctx->env Γ) type-out-out)
                                  (cons case0 case*))])
            (if (match-is-total (cons case0 case*))
            (go `(the ,type-out-out
                      ,(append `(match ,type-in-out ,type-out-out ,expr-out) (cons case0 case*))))
            (stop e "Match clause is not total. You must include an else case")))]
    [`(U ,n)
     (go `(the (U (add1 ,n)) (U ,n)))]
    [`(,(or 'Σ 'Sigma) ((,x ,A)) ,D)
     (go-on ([`(the ,A-type ,A-temp) (synth Γ A)]
             [`(U ,n) (U-check Γ A-type)]
             [A-out (check Γ A (UNI (val (ctx->env Γ) n)))]
             
             [`(the ,D-type ,D-temp) (synth (extend-ctx Γ x (val (ctx->env Γ) A-out)) D)]
             [`(U ,k) (U-check Γ D-type)]
             )
            

        (go `(the (U ,(greater-Nat n k)) (Σ ((,x ,A-temp)) ,D-temp))))]
    [`(car ,pr)
     (go-on ([`(the ,pr-ty ,pr-out) (synth Γ pr)]
             [`(the ,pr-ty-ty ,stuff) (synth Γ pr-ty)])
       (match (val (ctx->env Γ) pr-ty)
         [(SIGMA A D)
          (go `(the ,(read-back-norm Γ (THE (val (ctx->env Γ) pr-ty-ty) A)) (car ,pr-out)))]
         [non-SIGMA
          (stop e (format "Expected Σ, got ~v"
                          (read-back-norm Γ (THE (val (ctx->env Γ) pr-ty-ty) non-SIGMA))))]))]

    [`(cdr ,pr)
     (go-on ([`(the ,pr-ty ,pr-out) (synth Γ pr)]
             [`(the ,type-of-type ,ty) (synth Γ pr-ty)]
             [M-expr (go (match ty [`(,(or 'Σ 'Sigma) ((,x ,A)) ,M) M]))]
             [`(the ,d-type ,d) (synth Γ M-expr)])
       (match (val (ctx->env Γ) pr-ty)
         [(SIGMA A D)
          (define the-car (do-car (val (ctx->env Γ) pr-out)))
          (go `(the ,(read-back-norm Γ (THE (val (ctx->env Γ) d-type) (val-of-closure D the-car)))
                    (cdr ,pr-out)))]
         [non-SIGMA
          (stop e (format "Expected Σ, got ~v" (read-back-norm Γ (THE (val (ctx->env Γ) type-of-type) non-SIGMA))))]))]
    ['Nat (go '(the (U zero) Nat))]
    [`(List ,E)
     (go-on ([`(the ,tE ,vE) (synth Γ E)]

             [`(U ,n) (U-check Γ tE)]
             )
            (go `(the ,tE (List ,vE))))]

    [`(Vec ,E ,n)
     (go-on ([`(the ,tE ,vE) (synth Γ E)]
             [`(U ,k) (U-check Γ tE)]
             [nk (check Γ n (NAT))])
            (go `(the (U ,k) (Vec ,vE ,nk))))]

    [`(ind-Nat ,target ,motive ,base ,step)
     (go-on ([target-out (check Γ target (NAT))]
             [`(the (,(or 'Π 'Pi) ((,x ,A)) ,B) ,mot) (synth Γ motive)]
             [`(U ,n) (U-check Γ B)]
             [_ (check Γ target (val (ctx->env Γ) A))]
             [motive-val (go (val (ctx->env Γ) mot))]
             [base-out (check Γ base (do-ap motive-val (ZERO)))]
             [step-out (check Γ
                              step
                              (ind-Nat-step-type motive-val))])
       (go `(the ,(read-back-norm
                   Γ
                    (THE (UNI (ZERO))
                        (do-ap motive-val (val (ctx->env Γ) target-out))))
                        (ind-Nat ,target-out ,mot ,base-out ,step-out))))]

    [`(ind-List ,target ,motive ,base ,step)
     (go-on ([`(the ,target-t-t ,target-out-t) (synth Γ target)]
             [entry-t (go (match (val (ctx->env Γ) target-t-t) [(LIST E) E]))]
             [target-out (go target-out-t)]
             

             [`(the (,(or 'Π 'Pi) ((,x ,A)) ,B) ,mot) (synth Γ motive)]
             [`(U ,n) (U-check Γ B)]
             [k (check Γ target-out-t (val (ctx->env Γ) A))]
             [motive-val (go (val (ctx->env Γ) mot))]

             
             [base-out (check Γ base (do-ap motive-val (NIL)))]
             [step-out (check Γ
                              step
                              (ind-List-step-type motive-val entry-t))])

            (go `(the ,(read-back-norm
                   Γ
                   (THE (UNI (ZERO))
                        (do-ap motive-val (val (ctx->env Γ) target-out))))
                 (ind-List ,target-out ,mot ,base-out ,step-out))))]

    [`(ind-Vec ,n ,target ,motive ,base ,step)
     (go-on ([n-out (check Γ n (NAT))]
             [`(the ,target-t-t ,target-out-t) (synth Γ target)]
             [entry-t (go (match (val (ctx->env Γ) target-t-t) [(VEC E n) E]))]
             [target-out (go target-out-t)]
             
             [motive-out (check Γ motive (PI (NAT) (H-O-CLOS 'arg (lambda (arg) (PI (VEC entry-t arg) (H-O-CLOS 'n (lambda (_) (UNI (INFTY)))))))))]
             [motive-val (go (val (ctx->env Γ) motive-out))]
             
             [base-out (check Γ base (do-ap (do-ap motive-val (ZERO)) (VECNIL)))]
             [step-out (check Γ
                              step
                              (ind-Vec-step-type motive-val entry-t))])
            (go `(the ,(read-back-norm
                   Γ
                   (THE (UNI (ZERO))
                        (do-ap (do-ap motive-val (val (ctx->env Γ) n-out)) (val (ctx->env Γ) target-out))))
                 (ind-Vec ,n-out ,target-out ,motive-out ,base-out ,step-out))))]
    [`(= ,A ,from ,to)
     (go-on ([`(the ,A-t ,A-temp) (synth Γ A)]
             [`(U ,n) (U-check Γ A-t)]
             [A-val (go (val (ctx->env Γ) A))]
             [from-out (check Γ from A-val)]
             [to-out (check Γ to A-val)])
       (go `(the (U ,n) (= ,A-temp ,from-out ,to-out))))]
    [`(replace ,target ,motive ,base)
     (go-on ([`(the ,target-t ,target-out) (synth Γ target)])
       (match (val (ctx->env Γ) target-t)
         [(EQ A from to)
          (go-on ([motive-out
                   (check Γ
                          motive
                          (PI A (H-O-CLOS 'x (lambda (x) (UNI (INFTY))))))]
                  [motive-v (go (val (ctx->env Γ) motive-out))]
                  [base-out (check Γ base (do-ap motive-v from))])
            (go `(the ,(read-back-norm Γ (THE (UNI (INFTY)) (do-ap motive-v to)))
                      (replace ,target-out ,motive-out ,base-out))))]
         [non-EQ
          (stop target (format "Expected =, but type is ~a" non-EQ))]))]
    [`(,(or 'Π 'Pi) ((,x ,A)) ,B)
     
     (go-on ([`(the ,A-type ,A-temp) (synth Γ A)]
             [`(U ,n) (U-check Γ A-type)]
             [A-out (check Γ A (UNI (val (ctx->env Γ) n)))]
             
             [`(the ,B-type ,B-temp) (synth (extend-ctx Γ x (val (ctx->env Γ) A-out)) B)]
             [`(U ,k) (U-check Γ B-type)]
             )
            
    (go `(the (U ,(greater-Nat n k)) (Π ((,x ,A-temp)) ,B-temp))))]

    ['Trivial (go '(the (U zero) Trivial))]
    ['Absurd (go '(the (U zero) Absurd))]
    [`(ind-Absurd ,target ,motive)
     (go-on ([target-out (check Γ target (ABSURD))]
             [motive-out (check Γ motive (UNI (INFTY)))])
       (go `(the ,motive-out (ind-Absurd ,target-out ,motive-out))))]
    ['Atom (go '(the (U zero) Atom))]
    [`(,rator ,rand)
     (go-on ([`(the (,(or 'Π 'Pi) ((,k ,S)) ,M) ,rator-out) (synth Γ rator)]
             [`(the ,rator-t ,rator-out) (synth Γ rator)]
             [`(the ,rator-t-t ,temp) (synth Γ rator-t)]
             [`(U ,v) (U-check Γ rator-t-t)]
             [`(the ,M-type ,M-temp) (synth (extend-ctx Γ k (val (ctx->env Γ) S)) M)]
             [`(U ,g) (U-check Γ M-type)])

       (match (val (ctx->env Γ) rator-t)
         [(PI A B)
          (go-on ([rand-out (check Γ rand A)])
            (go `(the ,(read-back-norm Γ
                                        (THE (UNI (ZERO))
                                            (val-of-closure B
                                                            (val (ctx->env Γ)
                                                                 rand-out))))
                      (,rator-out ,rand-out))))]
         [non-PI (stop rator
                       (format "Expected a Π type, but this is a ~a"
                               (read-back-norm Γ (THE (UNI (val (ctx->env Γ) v)) non-PI))))]))]

    [x #:when (var? x)
     (go-on ([t (lookup-type x Γ)]
             [`(the ,t-type ,temp) (synth Γ (read-back-norm Γ (THE (UNI (ZERO)) t)))])
       (go `(the ,(read-back-norm Γ (THE (UNI (ZERO)) t)) ,x)))]
    [none-of-the-above (stop e "Can't synthesize a type")]))

(define (rec-synth Γ name e)
  (match e
    [`(the ,ty ,expr)
       (go-on ([synth-out (synth (extend-ctx Γ name (val (ctx->env Γ) ty)) e)]
               [expr-out
                (match synth-out
                  [`(the ,ty-out ,expr-out) (rec-check Γ name expr-out (val (ctx->env Γ) ty-out))])])
              (go synth-out))]))

(define (rec-check Γ name e t)
  (go-on ([match-out (check-recursive-form e)])
         (match match-out
           [`(match ,type-in ,type-out ,expr ,case0 ,case* ...)
             (if (rec-check-cases name (cons case0 case*))
                 (go e)
                 (stop e "The last argument of a recursive case must be a strict sub expression of the match pattern."))])))

(provide synth rec-synth)