#lang racket
 (require racket/trace)

;imports for chapter 4 error handling, specifically go-on
(require (for-syntax syntax/parse))
(require (for-syntax racket/base syntax/parse))
(require racket/trace)

; env : Env
; var : symbol?
; body : any/c
(struct CLOS (env var body) #:transparent)

; ρ : environment?
; x : symbol?
; v : value?
(define (extend p x v)
  (cons (cons x v) p))

; x : symbol?
(define (add-* x)
  (string->symbol
   (string-append (symbol->string x)
                  "*")))

; used : (listof symbol?)
; x : symbol?

(define (freshen used x)
  (if (memv x used)
      (freshen used (add-* x))
      x))

; result : any/c
(struct go (result) #:transparent)

; expr : expression?
; message : string?
(struct stop (expr message) #:transparent)

;
(define-syntax (go-on stx)
  (syntax-parse stx
    [(go-on () result)
     (syntax/loc stx
       result)]
    [(go-on ([pat0 e0] [pat e] ...) result)
     (syntax/loc stx
       (match e0
         [(go pat0) (go-on ([pat e] ...) result)]
         [(go v) (error 'go-on "Pattern did not match value ~v" v)]
         [(stop expr msg) (stop expr msg)]))]))


(struct ZERO () #:transparent)

(struct INFTY () #:transparent)

; pred : value
(struct ADD1 (pred) #:transparent)

(define keywords
  (list 'define
        'U
        'Nat 'zero 'add1 '+ 'ind-Nat
        'Σ 'Sigma 'cons 'car 'cdr
        'Π 'Pi 'λ 'lambda
        '= 'same 'replace
        'Trivial 'sole
        'Absurd 'ind-Absurd
        'Atom 'quote
        'the
        'List
        '::
        'nil
        'Vec
        'vecnil
        'vec::
        'ind-Vec
        'ind-List 
        'match
        'infty))

(define a-matchables
  (list 'zero 'Nat 'Atom 'List 'Vec 'nil 'vecnil 'U))

; x : keyword?
(define (keyword? x)
  (if (memv x keywords)
      #t
      #f))

(define (a-matchable? x)
  (if (or (or (memv x a-matchables) (list? x)) (arbitrary? x))
      #t
      #f))
  

; x : any/c
(define (var? x)
  (and (symbol? x)
       (not (keyword? x))))

; e1 : expression?
; e2 : expression?
(define (α-equiv? e1 e2)
  (α-equiv-aux e1 e2 '() '()))

; e1 : expression?
; e2 : expression?
; xs1 : (listof (pair symbol symbol))
; xs2 : (listof (pair symbol symbol))

(define (α-equiv-aux e1 e2 xs1 xs2)
  (match* (e1 e2)
    [(kw kw)
     #:when (keyword? kw)
     #t]
    [(x y)
     #:when (and (var? x) (var? y))
     (match* ((assv x xs1) (assv y xs2))
       [(#f #f) (eqv? x y)]
       [((cons _ b1) (cons _ b2)) (eqv? b1 b2)]
       [(_ _) #f])]
    [(`(λ (,x) ,b1) `(λ (,y) ,b2))
     (let ([fresh (gensym)])
       (let ([bigger1 (cons (cons x fresh) xs1)]
             [bigger2 (cons (cons y fresh) xs2)])
         (α-equiv-aux b1 b2 bigger1 bigger2)))]
    [(`(Π ((,x ,A1)) ,B1) `(Π ((,y ,A2)) ,B2))
     (and (α-equiv-aux A1 A2 xs1 xs2)
          (let ([fresh (gensym)])
            (let ([bigger1 (cons (cons x fresh) xs1)]
                  [bigger2 (cons (cons y fresh) xs2)])
              (α-equiv-aux B1 B2 bigger1 bigger2))))]
    [(`(Σ ((,x ,A1)) ,B1) `(Σ ((,y ,A2)) ,B2))
     (and (α-equiv-aux A1 A2 xs1 xs2)
          (let ([fresh (gensym)])
            (let ([bigger1 (cons (cons x fresh) xs1)]
                  [bigger2 (cons (cons y fresh) xs2)])
              (α-equiv-aux B1 B2 bigger1 bigger2))))]
    [(`',x  `',y)
     (eqv? x y)]

    [(`(the Absurd ,e1) `(the Absurd ,e2))
     #t]
    [((cons op args1) (cons op args2))
     #:when (keyword? op)
     (and (= (length args1) (length args2))
          (for/and ([arg1 (in-list args1)]
                    [arg2 (in-list args2)])
            (α-equiv-aux arg1 arg2 xs1 xs2)))]
    [((list rator1 rand1) (list rator2 rand2))
     (and (α-equiv-aux rator1 rator2 xs1 xs2)
          (α-equiv-aux rand1 rand2 xs1 xs2))]
    [(_ _) #f]))


(define (subtype? e1 e2)
  (α-subtype-aux e1 e2 '() '()))


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


; domain : value?
; range : closure?
(struct PI (domain range) #:transparent)
; body : closure?
(struct LAM (body) #:transparent)
; car-type : value?
; cdr-type : closure?
(struct SIGMA (car-type cdr-type) #:transparent)
; car : value?
; cdr : value?
(struct PAIR (car cdr) #:transparent)

(struct NAT () #:transparent)

; type : value?
; from : value?
; to : value?
(struct EQ (type from to) #:transparent)

(struct SAME () #:transparent)

(struct TRIVIAL () #:transparent)

(struct SOLE () #:transparent)

(struct ABSURD () #:transparent)

(struct ATOM () #:transparent)

; symbol : symbol?
(struct QUOTE (symbol) #:transparent)

(struct UNI (level) #:transparent)

(struct LIST (entry-type) #:transparent)
(struct NIL () #:transparent)
(struct CONCAT:: (head tail) #:transparent)


(struct VEC (entry-type len) #:transparent)
(struct VECNIL () #:transparent)
(struct VCAT:: (head tail) #:transparent)

; type : value?
; neutral : neutral?
(struct NEU (type neutral) #:transparent)

; x : symbol?
; fun : (-> value ? value?)
(struct H-O-CLOS (x fun) #:transparent)

; c : closure?
(define (closure-name c)
  (match c
    [(CLOS _ x _) x]
    [(H-O-CLOS x _) x]))

; name : symbol?
(struct N-var (name) #:transparent)

; fun : neutral?
; arg : normal?
(struct N-ap (fun arg) #:transparent)

; pair : neutral?
(struct N-car (pair) #:transparent)

; pair : neutral?
(struct N-cdr (pair) #:transparent)

; target : neutral?
; motive : normal?
; base : normal?
; step : normal?
(struct N-ind-Nat (target motive base step) #:transparent)


(struct N-ind-List (target motive base step) #:transparent)



(struct N-ind-Vec (n target motive base step) #:transparent)

; x : (or expr? neutral?)
; y : (or expr? neutral?)
(struct N-+ (x y) #:transparent)


; target : neutral?
; motive : normal?
; base : normal?
(struct N-replace (target motive base) #:transparent)

; target : neutral?
; motive : normal?
(struct N-ind-Absurd (target motive) #:transparent)

(struct N-match (type-in type-out expr case0 case*) #:transparent)

; type : value?
; val : value?
(struct THE (type val) #:transparent)

; type : value?
; value : value?
(struct def (type value) #:transparent)

; type : value?
(struct bind (type) #:transparent)

; x : symbol?
; Γ : context?

(define (lookup-type x Γ)
  (match (assv x Γ)
    [#f (stop x "Unknown variable")]
    [(cons _ (bind type)) (go type)]
    [(cons _ (def type _)) (go type)]))

; Γ : context?
(define (ctx->env Γ)
  (map (lambda (binder)
         (match binder
           [(cons name (bind type))
            (cons name
                  (NEU type
                       (N-var name)))]
           [(cons name (def _ value))
            (cons name value)]))
       Γ))

; Γ : context?
; x : symbol?
(define (extend-ctx Γ x t)
  (cons (cons x (bind t)) Γ))

; c : closure?
; v : value?
(define (val-of-closure c v)
  (match c
    [(CLOS ρ x e) (val (extend ρ x v) e)]
    [(H-O-CLOS x f) (f v)]))

(define (do-match ρ type-in type-out expr case0 case*)
  (if (NEU? expr)
      (NEU (val ρ type-out) (N-match type-in type-out (match expr [(NEU X ne) ne]) case0 case*))
      (let* ([expr-norm (read-back-norm ρ (THE (val ρ type-in) expr))]
             [case-out (match-cases expr-norm case0 case*)]
             [r-out (replace-arbitraries expr-norm case-out)])
        (val ρ (desugar r-out)))))

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

(define (b-list? e)
  (and (list? e) (match e [`',s #f] [else #t])))

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
    
; x : value?
(define (count-add1s x)
  (match x
    [(ZERO) 0]
    [(ADD1 n) (+ 1 (count-add1s n))]))

(define (create-add1s n e)
  (if (= n 0) e (ADD1 (create-add1s (- n 1) e))))


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

(define (check-result-type Γ m r type-in type-out m-a r-a)
  (if (empty? r-a)
      (check Γ r type-out)
      (let* ([a-to-f (arbitraries-to-fresh r-a Γ)]
             [extended-ctx (extend-ctx-arbitraries-to-fresh Γ m a-to-f type-in)]
             [r-out (replace-arbitraries-expr a-to-f r)])
        (check extended-ctx (desugar r-out) type-out))))
      
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

(define (get-recursive-calls name r)
  (cond
    [(b-list? r) (match r
                   [`(,r0 ,r* ...) (cond
                                     [(equal? name r0) `(,r)]
                                     [(b-list? r0) (append (get-recursive-calls name r0)
                                                           (get-recursive-calls name r*))]
                                     [else (get-recursive-calls name r*)])]
                   [`() `()])]
    [`() `()]))

(define (share-a-member L0 L1)
  (match L0
    [`(,e ,es ...) (cond
                     [(member e L1) #t]
                     [else (share-a-member es L1)])]
    [`() #f]))

(define (last-arg-strict-sub-expr m call)
  (match call
    [`() #f]
    [`(,e ,es ...)
     (let ([e-s (format "~a" e)]
           [m-s (format "~a" m)])
       (cond
         [(empty? es) (and (and (string-contains? m-s e-s) (string-contains? e-s "!"))
                                (< (string-length e-s) (string-length m-s)))]
         [else (last-arg-strict-sub-expr m es)]))]))

(define (all-calls-last-arg-strict-sub-expr m calls)
  (match calls
    [`() #t]
    [`(,c0 ,c* ...) (and (last-arg-strict-sub-expr m c0)
                         (all-calls-last-arg-strict-sub-expr m c*))]))

(define (rec-check-cases name cases)
  (match cases
    [`() #t]
    [`(,case0 ,case* ...)
     [match case0
       [`(,m ,r)
        (and (all-calls-last-arg-strict-sub-expr m (get-recursive-calls name r))
             (rec-check-cases name case*))]]]))
     

(define (check-recursive-form e)
  (match e
    [`(,(or 'λ 'lambda) (,expr) (match ,type-in ,type-out ,expr ,case0 ,case* ...))
     (go (append `(match ,type-in ,type-out ,expr) (cons case0 case*)))]
    [`(,(or 'λ 'lambda) (,x) ,b) (check-recursive-form b)]
    [else
     (stop e "Recursive functions must be of the form (λ (x y ... z) (match A B z ...))")]))

(define (rec-check Γ name e t)
  (go-on ([match-out (check-recursive-form e)])
         (match match-out
           [`(match ,type-in ,type-out ,expr ,case0 ,case* ...)
             (if (rec-check-cases name (cons case0 case*))
                 (go e)
                 (stop e "The last argument of a recursive case must be a strict sub expression of the match pattern."))])))
                        
(define (rec-synth Γ name e)
  (match e
    [`(the ,ty ,expr)
       (go-on ([synth-out (synth (extend-ctx Γ name (val (ctx->env Γ) ty)) e)]
               [expr-out
                (match synth-out
                  [`(the ,ty-out ,expr-out) (rec-check Γ name expr-out (val (ctx->env Γ) ty-out))])])
              (go synth-out))]))

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





; Γ : context?
; e : expr?
; t : value?


(define (U-check Γ expr)
  (match expr
    [`(U ,n) (go `(U ,n))]
    [non-U (stop expr (format "Expected (U n) got ~v" (read-back-norm Γ (val (ctx->env Γ) (synth Γ expr) non-U))))]))


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

(define (subtype-convert Γ lvl t1 t2)
  (define e1 (read-back-norm Γ (THE (UNI (ZERO)) t1)))
  (define e2 (read-back-norm Γ (THE (UNI (ZERO)) t2)))
  (if (subtype? e1 e2)
      (go 'ok)
      (stop e1 (format "Expected to be the same ~v as ~v"
                       `(add1 ,lvl)
                       e2))))

; Γ : context?
; input : (or/c (list/c 'define symbol? expression?) expression?)

(define (interact Γ input)
  (match input
    [`(define ,x ,e)
     (if (assv x Γ)
         (stop x "Already defined")        
         (go-on ([`(the ,ty ,expr)
                  (if (string-prefix? (symbol->string x) "rec-")
                      (rec-synth Γ x (desugar e))
                      (synth Γ (desugar e)))])
           (let ([ρ (ctx->env Γ)])
             (go (cons (cons x (def (val ρ ty) (val ρ expr)))
                       Γ)))))]
    [e
     (go-on ([`(the ,ty ,expr) (synth Γ (desugar e))])
       (let ([ρ (ctx->env Γ)])
         (begin
           (printf "Type: ~v\nNormal form:~v\n"
                   ty
                   (read-back-norm Γ
                                   (THE (val ρ ty)
                                        (val ρ expr))))
           (go Γ))))]))


(define (run-program Γ inputs)
  (match inputs
    ['() (go Γ)]
    [(cons d rest)
     (go-on ([new-Γ (interact Γ d)])
       (run-program new-Γ rest))]))

; s : expr?
(define (desugar e)
  (match e
    [`(the ,A ,x) `(the ,(desugar A) ,(desugar x))]
    [`(,(or 'λ 'lambda) (,x ,y ...) ,b) (desugar-λ e)]
    [`(,(or 'Π 'Pi) (,d0 ,d1 ...) ,range) (desugar-Π e)]
    [`(,rator ,rand) #:when (not (keyword? rator)) `(,(desugar rator) ,(desugar rand))]
    [`(,rator ,rand0 ,rand1 ...) #:when (not (keyword? rator)) (desugar `,(cons `(,rator ,rand0) rand1))]
    [`(,keyword ,rand0 ,rand1 ...) `,(cons keyword (cons (desugar rand0) (desugar-rands rand1)))]                 
    [_ e]))
  

; e : expr?
(define (desugar-λ e)
  (match e
    [`(,(or 'λ 'lambda) (,x ,y ,z ...) ,b)
     `(λ (,x) ,(desugar-λ `(λ ,(cons y z) ,b)))]
    [not-sugared e]))

(define (desugar-Π e)
  (match e
    [`(,(or 'Π 'Pi) (,d0 ,d1 ,d2 ...) ,range)
     `(Π (,d0) ,(desugar-Π `(Π ,(cons d1 d2) ,range)))]
    [not-sugared e]))

(define (desugar-rands e)
  (match e
    [`(,rand0 ,rand1 ...) `,(cons (desugar rand0) (desugar-rands rand1))]
    [rand0 (desugar rand0)]))

; -----------------------------------------------------------

(provide (all-defined-out))
                                                  