#lang racket

;imports for chapter 4 error handling, specifically go-on
(require (for-syntax syntax/parse))
(require (for-syntax racket/base syntax/parse))


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

(define (norm ρ e)
  (read-back '() (val ρ e)))

; e : expression?
(define (with-numerals e)
  `((define church-zero
      (λ (f)
        (λ (x)
          x)))
    (define church-add1
      (λ (n-1)
        (λ (f)
          (λ (x)
            (f ((n-1 f) x))))))
    ,e))

; n : exact-nonnegative-integer?
(define (to-church n)
  (cond [(zero? n) 'church-zero]
        [(positive? n)
         (let ([church-of-n-1 (to-church (sub1 n))])
           `(church-add1 ,church-of-n-1))]))

(define church-add
  `(λ (j)
     (λ (k)
       (λ (f)
         (λ (x)
           ((j f) ((k f) x)))))))


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

; t1 : any/c
; t2 : any/c
(define (type=? t1 t2)
  (match* (t1 t2)
    [('Nat 'Nat) #t]
    [(`(→ ,A1 ,B1) `(→ ,A2 ,B2))
     (and (type=? A1 A2) (type=? B1 B2))]
    [(_ _) #f]))

; t : any/c
(define (type? t)
  (type=? t t))

; Γ : context?
; prog : (listof (or/c expression? (list/c 'define symbol? expression?)))
(define (check-program Γ prog)
  (match prog
    ['()
     (go Γ)]
    [(cons `(define ,x ,e) rest)
     (go-on ([t (synth Γ e)])
       (check-program (extend Γ x t) rest))]
    [(cons e rest)
     (go-on ([t (synth Γ e)])
       (begin
         (printf "~a has type ~a\n" e t)
         (check-program Γ rest)))]))



(struct ZERO () #:transparent)

; pred : value
(struct ADD1 (pred) #:transparent)


; type : type?
; target : neutral?
; base : norm?
; step : norm?
(struct	N-rec (type target base step) #:transparent)

; v : any/c
(define (norm? v) (THE? v))

; type : type?
; target : value?
; base : value?
; step : value?
(define (do-rec type target base step)
  (match target
    [(ZERO) base]
    [(ADD1 n)
     (do-ap (do-ap step n)
            (do-rec type n base step))]
    [(NEU 'Nat ne)
     (NEU type
          (N-rec type
                 ne
                 (THE type base)
                 (THE `(→ Nat (→ ,type ,type)) step)))]))

; used-names : (listof symbol?)
; type : type?
; value : value?
(define (read-back used-names type value)
  (match type
    ['Nat
     (match value
       [(ZERO) 'zero]
       [(ADD1 n) `(add1 ,(read-back used-names 'Nat n))]
       [(NEU _ ne)
        (read-back-neutral used-names ne)])]
    [`(→ ,A ,B)
     (let ([x (freshen used-names 'x)])
       `(λ (,x)
          ,(read-back (cons x used-names)
                      B
                      (do-ap value (NEU A (N-var x))))))]))

; Δ : definitions?
(define (defs->ctx Δ)
  (match Δ
    ['() '()]
    [(cons (cons x (def type _)) rest)
     (extend (defs->ctx rest) x type)]))

; Δ : definitions?
(define (defs->env Δ)
  (match Δ
    ['() '()]
    [(cons (cons x (def _ value)) rest)
     (extend (defs->env rest) x value)]))

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
        'the 'match))

(define a-matchables
  (list 'zero 'Nat 'Atom))

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
    ; This, together with read-back-norm, implements the η law for Absurd.
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

(struct UNI () #:transparent)

; type : value?
; neutral : neutral?
(struct NEU (type neutral) #:transparent)

; x : symbol?
; fun : (-> value ? value?)
(struct H-O-CLOS (x fun) #:transparent)

; c : any/c
(define (closure? c)
  (or (CLOS? c) (H-O-CLOS? c)))

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

; Γ : any/c
(define (context? Γ)
  (match Γ
    ['() #t]
    [(cons (cons x b) rest)
     (and (symbol? x) (or (def? b) (bind? b)) (context? rest))]
    [_ #f]))

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
        (val ρ r-out))))

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
    ['U (UNI)]
    [`(,(or 'Π 'Pi) ((,x ,A)) ,B)
     (PI (val ρ A) (CLOS ρ x B))]
    [`(λ (,x) ,b)
     (LAM (CLOS ρ x b))]
    [`(Σ ((,x ,A)) ,D)
     (SIGMA (val ρ A) (CLOS ρ x D))]
    [`(cons ,a ,d)
     (PAIR (val ρ a) (val ρ d))]
    [`(car ,pr)
     (do-car (val ρ pr))]
    [`(cdr ,pr)
     (do-cdr (val ρ pr))]
    ['Nat (NAT)]
    ['zero (ZERO)]
    [`(add1 ,n) (ADD1 (val ρ n))]
    [`(+ ,x ,y) (do-+ (val ρ x) (val ρ y))]
    [`(ind-Nat ,target ,motive ,base ,step)
     (do-ind-Nat (val ρ target) (val ρ motive) (val ρ base) (val ρ step))]
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
     (cdr (assv x ρ))]))

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
     (NEU motive (N-ind-Absurd ne (THE (UNI) motive)))]))

; target : value?
; motive : value?
; base : value?

(define (do-replace target motive base)
  (match target
    [(SAME) base]
    [(NEU (EQ A from to) ne)
     (NEU (do-ap motive to)
          (N-replace ne
                     (THE (PI A (H-O-CLOS 'x (lambda (_) (UNI))))
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
                    (H-O-CLOS 'k (lambda (k) (UNI))))
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
; Γ : context?
; norm : norm?

(define (read-back-norm Γ norm)
  (match norm
    [(THE (NAT) (ZERO)) 'zero]
    [(THE (NAT) (ADD1 n))
     `(add1 ,(read-back-norm Γ (THE (NAT) n)))]
   
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
    [(THE (UNI) (NAT)) 'Nat]
    [(THE (UNI) (ATOM)) 'Atom]
    [(THE (UNI) (TRIVIAL)) 'Trivial]
    [(THE (UNI) (ABSURD)) 'Absurd]
    [(THE (UNI) (EQ A from to))
     `(= ,(read-back-norm Γ (THE (UNI) A))
         ,(read-back-norm Γ (THE A from))
         ,(read-back-norm Γ (THE A to)))]
    [(THE (UNI) (SIGMA A D))
     (define x (closure-name D))
     (define y (freshen (map car Γ) x))
     `(Σ ((,y ,(read-back-norm Γ (THE (UNI) A))))
         ,(read-back-norm (extend-ctx Γ y A)
                          (THE (UNI) (val-of-closure D (NEU A (N-var y))))))]
    [(THE (UNI) (PI A B))
     (define x (closure-name B))
     (define y (freshen (map car Γ) x))
     `(Π ((,y ,(read-back-norm Γ (THE (UNI) A))))
         ,(read-back-norm (extend-ctx Γ y A)
                          (THE (UNI) (val-of-closure B (NEU A (N-var y))))))]
    [(THE (UNI) (UNI)) 'U]
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
        (check extended-ctx r-out type-out))))
      
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

(define (atleast-one-strict-sub-expr m call)
  (match call
    [`() #f]
    [`(,e ,es ...)
     (let ([e-s (format "~a" e)]
           [m-s (format "~a" m)])
     (or (and (string-contains? m-s e-s) (< (string-length e-s) (string-length m-s)))
                       (atleast-one-strict-sub-expr m es)))]))

(define (all-calls-strict-sub-expr m calls)
  (match calls
    [`() #t]
    [`(,c0 ,c* ...) (and (atleast-one-strict-sub-expr m c0) (all-calls-strict-sub-expr m c*))]))

(define (rec-check-cases name cases)
  (match cases
    [`() #t]
    [`(,case0 ,case* ...)
     [match case0
       [`(,m ,r)
        (and (all-calls-strict-sub-expr m (get-recursive-calls name r)) (rec-check-cases name case*))]]]))
     

(define (check-recursive-form e)
  (match e
    [`(,(or 'λ 'lambda) (,x) (match ,type-in ,type-out ,expr ,case0 ,case* ...))
     (go (append `(match ,type-in ,type-out ,expr) (cons case0 case*)))]
    [`(,(or 'λ 'lambda) (,x) ,b) (check-recursive-form b)]
    [else
     (stop e "Recursive functions must be of the form (λ (x y ...) (match ...))")]))

(define (rec-check Γ name e t)
  (go-on ([match-out (check-recursive-form e)])
         (match match-out
           [`(match ,type-in ,type-out ,expr ,case0 ,case* ...)
             (if (rec-check-cases name (cons case0 case*))
                 (go e)
                 (stop e "All recursive cases must have atleast one sub-expr as an argument"))])))
                        
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
     (go-on ([t-out (check Γ type (UNI))]
             [e-out (check Γ expr (val (ctx->env Γ) t-out))])
       (go `(the ,t-out ,e-out)))]    
    [`(match ,type-in ,type-out ,expr ,case0 ,case* ...)
     (go-on ([type-in-out (check Γ type-in (UNI))]
             [type-out-out (check Γ type-out (UNI))]
             [expr-out (check Γ expr (val (ctx->env Γ) type-in-out))]
             [cases-out
              (check-cases Γ (val (ctx->env Γ) type-in-out) (val (ctx->env Γ) type-out-out)
                                  (cons case0 case*))])
            (if (match-is-total (cons case0 case*))
            (go `(the ,type-out-out
                      ,(append `(match ,type-in-out ,type-out-out ,expr-out) (cons case0 case*))))
            (stop e "Match clause is not total. You must include an else case")))]
    ['U
     (go '(the U U))]
    [`(,(or 'Σ 'Sigma) ((,x ,A)) ,D)
     (go-on ([A-out (check Γ A (UNI))]
             [D-out (check (extend-ctx Γ x (val (ctx->env Γ) A-out)) D (UNI))])
       (go `(the U (Σ ((,x ,A-out)) ,D-out))))]
    [`(car ,pr)
     (go-on ([`(the ,pr-ty ,pr-out) (synth Γ pr)])
       (match (val (ctx->env Γ) pr-ty)
         [(SIGMA A D)
          (go `(the ,(read-back-norm Γ (THE (UNI) A)) (car ,pr-out)))]
         [non-SIGMA
          (stop e (format "Expected Σ, got ~v"
                          (read-back-norm Γ (THE (UNI) non-SIGMA))))]))]
    [`(cdr ,pr)
     (go-on ([`(the ,pr-ty ,pr-out) (synth Γ pr)])
       (match (val (ctx->env Γ) pr-ty)
         [(SIGMA A D)
          (define the-car (do-car (val (ctx->env Γ) pr-out)))
          (go `(the ,(read-back-norm Γ (THE (UNI) (val-of-closure D the-car)))
                    (cdr ,pr-out)))]
         [non-SIGMA
          (stop e (format "Expected Σ, got ~v"
                          (read-back-norm Γ (THE (UNI) non-SIGMA))))]))]
    ['Nat (go '(the U Nat))]
    [`(ind-Nat ,target ,motive ,base ,step)
     (go-on ([target-out (check Γ target (NAT))]
             [motive-out (check Γ motive (PI (NAT) (H-O-CLOS 'n (lambda (_) (UNI)))))]
             [motive-val (go (val (ctx->env Γ) motive-out))]
             [base-out (check Γ base (do-ap motive-val (ZERO)))]
             [step-out (check Γ
                              step
                              (ind-Nat-step-type motive-val))])
       (go `(the ,(read-back-norm
                   Γ
                   (THE (UNI)
                        (do-ap motive-val (val (ctx->env Γ) target-out))))
                 (ind-Nat ,target-out ,motive-out ,base-out ,step-out))))]
    [`(= ,A ,from ,to)
     (go-on ([A-out (check Γ A (UNI))]
             [A-val (go (val (ctx->env Γ) A-out))]
             [from-out (check Γ from A-val)]
             [to-out (check Γ to A-val)])
       (go `(the U (= ,A-out ,from-out ,to-out))))]
    [`(replace ,target ,motive ,base)
     (go-on ([`(the ,target-t ,target-out) (synth Γ target)])
       (match (val (ctx->env Γ) target-t)
         [(EQ A from to)
          (go-on ([motive-out
                   (check Γ
                          motive
                          (PI A (H-O-CLOS 'x (lambda (x) (UNI)))))]
                  [motive-v (go (val (ctx->env Γ) motive-out))]
                  [base-out (check Γ base (do-ap motive-v from))])
            (go `(the ,(read-back-norm Γ (THE (UNI) (do-ap motive-v to)))
                      (replace ,target-out ,motive-out ,base-out))))]
         [non-EQ
          (stop target (format "Expected =, but type is ~a" non-EQ))]))]
    [`(,(or 'Π 'Pi) ((,x ,A)) ,B)
     (go-on ([A-out (check Γ A (UNI))]
             [B-out (check (extend-ctx Γ x (val (ctx->env Γ) A-out)) B (UNI))])
       (go `(the U (Π ((,x ,A-out)) ,B-out))))]
    ['Trivial (go '(the U Trivial))]
    ['Absurd (go '(the U Absurd))]
    [`(ind-Absurd ,target ,motive)
     (go-on ([target-out (check Γ target (ABSURD))]
             [motive-out (check Γ motive (UNI))])
       (go `(the ,motive-out (ind-Absurd ,target-out ,motive-out))))]
    ['Atom (go '(the U Atom))]
    [`(,rator ,rand)
     (go-on ([`(the ,rator-t ,rator-out) (synth Γ rator)])
       (match (val (ctx->env Γ) rator-t)
         [(PI A B)
          (go-on ([rand-out (check Γ rand A)])
            (go `(the ,(read-back-norm Γ
                                       (THE (UNI)
                                            (val-of-closure B
                                                            (val (ctx->env Γ)
                                                                 rand-out))))
                      (,rator-out ,rand-out))))]
         [non-PI (stop rator
                       (format "Expected a Π type, but this is a ~a"
                               (read-back-norm Γ (THE (UNI) non-PI))))]))]
    [x #:when (var? x)
     (go-on ([t (lookup-type x Γ)])
       (go `(the ,(read-back-norm Γ (THE (UNI) t)) ,x)))]
    [none-of-the-above (stop e "Can't synthesize a type")]))


; Γ : context?
; e : expr?
; t : value?

(define (check Γ e t)
  (match e
    [`(cons ,a ,d)
     (match t
       [(SIGMA A D)
        (go-on ([a-out (check Γ a A)]
                [d-out (check Γ d (val-of-closure D (val (ctx->env Γ) a-out)))])
          (go `(cons ,a-out ,d-out)))]
       [non-SIGMA (stop e (format "Expected Σ, got ~v"
                                  (read-back-norm Γ (THE (UNI) non-SIGMA))))])]
    ['zero
     (match t
       [(NAT) (go 'zero)]
       [non-NAT (stop e (format "Expected Nat, got ~v"
                                (read-back-norm Γ (THE (UNI) non-NAT))))])]
    [`(add1 ,n)
     (match t
       [(NAT)
        (go-on ([n-out (check Γ n (NAT))])
          (go `(add1 ,n-out)))]
       [non-NAT (stop e (format "Expected Nat, got ~v"
                                (read-back-norm Γ (THE (UNI) non-NAT))))])]
    [`(+ ,x ,y)
     (match t
       [(NAT)
        (go-on ([x-out (check Γ x (NAT))] [y-out (check Γ y (NAT))])
               (go `(+ ,x-out ,y-out)))]
       [non-NAT (stop e (format "Expected Nat, got ~v"
                                (read-back-norm Γ (THE (UNI) non-NAT))))])]
    
    ['same
     (match t
       [(EQ A from to)
        (go-on ([_ (convert Γ A from to)])
          (go 'same))]
       [non-= (stop e (format "Expected =, got ~v"
                              (read-back-norm Γ (THE (UNI) non-=))))])]
    ['sole
     (match t
       [(TRIVIAL)
        (go 'sole)]
       [non-Trivial (stop e (format "Expected Trivial, got ~v"
                                    (read-back-norm Γ (THE (UNI) non-Trivial))))])]
    [`(,(or 'λ 'lambda) (,x) ,b)
     (match t
       [(PI A B)
        (define x-val (NEU A (N-var x)))
        (go-on ([b-out (check (extend-ctx Γ x A) b (val-of-closure B x-val))])
          (go `(λ (,x) ,b-out)))]
       [non-PI (stop e (format "Expected Π, got ~v"
                               (read-back-norm Γ (THE (UNI) non-PI))))])]
    [`',a
     (match t
       [(ATOM)
        (go `',a)]
       [non-ATOM (stop e (format "Expected Atom, got ~v"
                                 (read-back-norm Γ (THE (UNI) non-ATOM))))])]
    [none-of-the-above
     (go-on ([`(the ,t-out ,e-out) (synth Γ e)]
             [_ (convert Γ (UNI) t (val (ctx->env Γ) t-out))])
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
                       (read-back-norm Γ (THE (UNI) t))
                       e2))))




; Γ : context?
; input : (or/c (list/c 'define symbol? expression?) expression?)

(define (interact Γ input)
  (match input
    [`(define ,x ,e)
     (if (assv x Γ)
         (stop x "Already defined")
         (go-on ([`(the ,ty ,expr) (synth Γ (desugar e))])
           (let ([ρ (ctx->env Γ)])
             (go (cons (cons x (def (val ρ ty) (val ρ expr)))
                       Γ)))))]
    [`(rec-define ,x ,e)
    (if (assv x Γ)
         (stop x "Already defined")
         (go-on ([`(the ,ty ,expr) (rec-synth Γ x (desugar e))])
           (let* ([ρ (ctx->env Γ)]
                  [new-Γ (cons (cons x (def (val ρ ty) (val ρ expr))) Γ)]
                  [new-ρ (ctx->env new-Γ)])
             (go (cons (cons x (def (val new-ρ ty) (val new-ρ expr)))
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


















