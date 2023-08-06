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
        'the
        ;added List nil and double colon
        'List
        '::
        'nil
        ;adding vector vecnil and vec::
        'Vec
        'vecnil
        'vec::
        'ind-Vec
        'ind-List 
        'match))

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
    ;[(`(U (add1 ,n1)) `(U (add1 ,n2))) (α-equiv-aux `(U ,n1) `(U ,n2))]
    ;[(`(U (add1 ,n1)) `(U ,n2)) (α-equiv-aux `(U ,n1) `(U ,n2))]
    ;[(`(U (add1 ,n1)) `(U ,n2)) (α-equiv-aux `(U ,n1) `(U ,n2))]
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


(define (subtype? e1 e2)
  (α-subtype-aux e1 e2 '() '()))

;;;;;;;;;;;;;;;;;;;;;;SUBTYPER
(define (α-subtype-aux e1 e2 xs1 xs2)
  (match* (e1 e2)
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
    ; This, together with read-back-norm, implements the η law for Absurd.
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (greater-Nat-t A B)
  (match* (A B)
    [(`(add1 ,n ) `(add1 ,k ))  `(greater-Nat k n)]
    [(`zero `(add1 ,k)) #f]
    [(`(add1 ,k) zero) #t]))

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

;VECTOR: adding struct vecnil vcat:: and VEC
(struct VEC (entry-type len) #:transparent)
(struct VECNIL () #:transparent)
(struct VCAT:: (head tail) #:transparent)

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

;making a struct for ind-List
(struct N-ind-List (target motive base step) #:transparent)


;making a struct for ind-Vec
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
    ;[`(λ (,x) ,b)
    ;added an or expression for the lambda
    [`(,(or 'λ 'lambda) (,x) ,b)
     (LAM (CLOS ρ x b))]
    [`(Σ ((,x ,A)) ,D)
     (SIGMA (val ρ A) (CLOS ρ x D))]
    [`(cons ,a ,d)
     (PAIR (val ρ a) (val ρ d))]
    ;added List expression
    [`(List ,E) (LIST (val ρ E))]
    ;added :: expression, not super sure if the pattern is correct
    [`(:: ,head ,tail) (CONCAT:: (val ρ head) (val ρ tail))]
    ;added NIL expression
    ['nil (NIL)]
    ;added Vec expression
    [`(Vec ,E ,n) (VEC (val ρ E) (val ρ n))]
    [`(vec:: ,head ,tail) (VCAT:: (val ρ head) (val ρ tail))]
    ['vecnil (VECNIL)]
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
    ;evaluating a ind-List expression
    [`(ind-List ,target ,motive ,base, step)
     (do-ind-List (val ρ target) (val ρ motive) (val ρ base) (val ρ step))]
    ;evaluating a ind-Vec expression
    [`(ind-Vec ,n ,target ,motive ,base, step)
     (do-ind-Vec (val ρ n) (val ρ target) (val ρ motive) (val ρ base) (val ρ step))]
    [`(= ,A ,from ,to)
     (EQ (val ρ A) (val ρ from) (val ρ to))]
    ['same
     (SAME)]
    ;it might be necessary to synthesize the motive to know the type of certain things,
    ;but this could mean excessive annotations unfortunately so you should test it out a bit
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

;added uni arg, what if i want to be able to show that it implies statements of higher types??
;okay now you have to add a (the blah blah) when describing ur motive lol
;alright new update, it seems as if the UNI ZERO part here is only for the purposes of readback neutral
;and readback neutral doesn't really care about the type of the UNI, so it seems like it would actually be fine
;if i just left the UNI ZERO here even thought i can use types which involve higher uni levels
(define (do-ind-Absurd target motive)
  (match target
    [(NEU (ABSURD) ne)
     (NEU motive (N-ind-Absurd ne (THE (UNI (ZERO)) motive)))]))

; target : value?
; motive : value?
; base : value?


;i think ill need to synth the type of the motive if im allowing the motive to return higher types like U_1 etc.
;update: once again it seems that this uni thing in the h-o-clos doesnt actually get used and it goes into the readback neutral eventualy
;but the readbacknorm doesn't use it
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

;similar to the other do-functions, the hard coded UNI is not proper, but its unnecessary to make the n-value correct
;since it eventually endds up in readbacknorm or something which doesn't care about the actual n value
(define (do-ind-Nat target motive base step)
  (match target
    [(ZERO) base]
    [(ADD1 n) (do-ap (do-ap step n) (do-ind-Nat n motive base step))]
    [(NEU (NAT) ne)
     (NEU (do-ap motive target)
          (N-ind-Nat
           ne
           (THE (PI (NAT)
                    (H-O-CLOS 'k (lambda (k) (UNI (ZERO)))))
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
;writing the code which actually returns the value of the ind-List
;expression provided the values of the arguments
(define (do-ind-List target motive base step)
  (match target
    [(NIL) base]
    [(CONCAT:: hed res) (do-ap (do-ap (do-ap step hed) res) (do-ind-List res motive base step))]
    [(NEU (LIST E) ne)
     (NEU (do-ap motive target)
          (N-ind-List
           ne
           (THE (PI (LIST E)
                    (H-O-CLOS 'k (lambda (k) (UNI))))
                motive)
           (THE (do-ap motive (NIL)) base)
           (THE (ind-List-step-type motive E)
                step)))]))
(define (ind-List-step-type motive E)
  ;removed brackets from around E on line 735
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


;writing the code which actually returns the value of the ind-Vec
;expression provided the values of the arguments
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
                    (H-O-CLOS 'k (lambda (k) (UNI)))))))
                motive)
           (THE (do-ap (do-ap motive (ZERO)) (VECNIL)) base)
           (THE (ind-Vec-step-type motive E)
                step)))]))

(define (ind-Vec-step-type motive E)
  ;removed brackets from around E on line 735
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

;added some (UNI n)s but this might have to be modified slightly
;alright, so it doesn't even seem like this function ever cares about the UNI type
(define (read-back-norm Γ norm)
  (match norm
    [(THE (NAT) (ZERO)) 'zero]
    [(THE (NAT) (ADD1 n))
     `(add1 ,(read-back-norm Γ (THE (NAT) n)))]
    ;adding readback for nil
    [(THE (LIST E) (NIL)) 'nil]
    ;adding readback for ::
    [(THE (LIST E) (CONCAT:: hed tal)) `(:: ,(read-back-norm Γ (THE E hed)) ,(read-back-norm Γ (THE (LIST E) tal)))]
    ;adding readback for vecnil
    [(THE (VEC E n) (VECNIL)) 'vecnil]
    ;adding readback for vec::
    [(THE (VEC E (ADD1 n)) (VCAT:: hed tal)) `(vec:: ,(read-back-norm Γ (THE E hed)) ,(read-back-norm Γ (THE (VEC E n) tal)))]
    [(THE (PI A B) f)
     (define x (closure-name B))
     (define y (freshen (map car Γ) x))
     ;note that the (THE (val-of-closure B y-val) shouldn't be like super important for anything here,
     ;since readbacknormm doesn't care about the n in the (U n) annotation
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
    ;adding readback for the actual type name List E
    [(THE (UNI n) (LIST E)) `(List ,(read-back-norm Γ (THE (UNI) E)))]
    ;adding readbackk for the actual type name Vec E n
    [(THE (UNI n) (VEC E n)) `(Vec ,(read-back-norm Γ (THE (UNI) E)) ,(read-back-norm Γ (THE (NAT) n)))]
    [(THE (UNI n) (NAT)) 'Nat]
    [(THE (UNI n) (ATOM)) 'Atom]
    [(THE (UNI n) (TRIVIAL)) 'Trivial]
    [(THE (UNI n) (ABSURD)) 'Absurd]
    [(THE (UNI n) (EQ A from to))
     `(= ,(read-back-norm Γ (THE (UNI n) A))
         ,(read-back-norm Γ (THE A from))
         ,(read-back-norm Γ (THE A to)))]
    ;the issue here might be that A is a (UNI n) and D is a lower UNI by im assignning them both the high UNI, this is a
    ;variance rules thing
    ;update: i dont think that readbacknorm cares about uni type
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
    ;over here i dont think its required to enforce that k>n, that should maybe be done in another function??
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
    ;added the readback for a ind-List expression
    ;but this once again is reading back step as a normal expression, but what if its neutral?
    [(N-ind-List ne motive base step)
     `(ind-List ,(read-back-neutral Γ ne)
               ,(read-back-norm Γ motive)
               ,(read-back-norm Γ base)
               ,(read-back-norm Γ step))]

    ;added the readback for a ind-Vec expression
    ;not sure whether to read both n and ne as neutral or pick one of them, should test both
    ;what if readback norm just defaults to readback neutral if its actually neutral?
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
             ;this next line might be useless, why not just use typeoftype?
             ;edit: in the above line I dont think i mean typeoftype, i think i mean ,ty instead of t-out in the return expression
             ;going to only have the U-check on typeoftype this will allow somthing like (the (Pi((n Nat)) (U (add1 n))) (lambda(n) (U n))).
             ;it just guarentees that type is a (U something), but it can be parameterized like in the above example
             ;[t-out (check Γ type (UNI (val (ctx->env Γ) n)))]
             ;[e-out (check Γ expr (val (ctx->env Γ) t-out))])
            [e-out (check Γ expr (val (ctx->env Γ) ty))])
        (go `(the ,ty ,e-out)))]
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
    [`(U ,n)
     (go `(the (U (add1 ,n)) (U ,n)))]
    [`(,(or 'Σ 'Sigma) ((,x ,A)) ,D)
     (go-on ([`(the ,A-type ,A-temp) (synth Γ A)]
             [`(U ,n) (U-check Γ A-type)]
             [A-out (check Γ A (UNI (val (ctx->env Γ) n)))]
             
             [`(the ,D-type ,D-temp) (synth (extend-ctx Γ x (val (ctx->env Γ) A-out)) D)]
             [`(U ,k) (U-check Γ D-type)]
             ;some of these parts were commented out in a similar way to Pi
             ;[D-out (check (extend-ctx Γ x (val (ctx->env Γ) A-out)) D (UNI (check Γ A (UNI (val (ctx->env Γ) n)))))]
             )
            
       ;(go `(the (U ,(greater-Nat (cdr (cdr A-out)) (cdr (cdr D-out)))) (Σ ((,x ,(car A-out))) ,(car D-out)))))]
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
    ;spaghetti! this can definitely be cut down a bit
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
    ;need to change U list
    ;Adding synthesizing for List
    [`(List ,E)
     (go-on ([Ek (check Γ E (UNI))]) (go `(the U (List ,Ek))))]
    ;adding synthesizing for Vec
    [`(Vec ,E ,n)
     (go-on ([Ek (check Γ E (UNI))] [nk (check Γ n (NAT))]) (go `(the U (Vec ,Ek ,nk))))]

    [`(ind-Nat ,target ,motive ,base ,step)
     (go-on ([target-out (check Γ target (NAT))]
             [`(the (,(or 'Π 'Pi) ((,x ,A)) ,B) ,mot) (synth Γ motive)]
             [`(U ,n) (U-check Γ B)]
             ;since im already synthesizing the motive and confirming that B is a U, then do i really need to check the motive against this type?
             ;[motive-out (check Γ motive (PI (NAT) (H-O-CLOS 'n (lambda (_) (UNI (val (ctx->env Γ) n))))))]
             ;[motive-val (go (val (ctx->env Γ) motive-out))]
             [motive-val (go (val (ctx->env Γ) mot))]
             [base-out (check Γ base (do-ap motive-val (ZERO)))]
             [step-out (check Γ
                              step
                              (ind-Nat-step-type motive-val))])
       ;in the next line im just going to replace UNI val... with UNI zero, because i dont think that read-back-norm cares about uni type
       (go `(the ,(read-back-norm
                   Γ
                   ;(THE (UNI (val (ctx->env Γ) n))
                    (THE (UNI (ZERO))
                        (do-ap motive-val (val (ctx->env Γ) target-out))))
                        (ind-Nat ,target-out ,mot ,base-out ,step-out))))]
;need to change U list
    ;adding synthesizing for ind-List
    ;note that it needs to be figured out what the type of the list entries are, for now theres the
    ;assumption that the target has the form `(the A B)
    [`(ind-List ,target ,motive ,base ,step)
     (go-on ([`(the ,target-t-t ,target-out-t) (synth Γ target)]
             [entry-t (go (match (val (ctx->env Γ) target-t-t) [(LIST E) E]))]
             [target-out (go target-out-t)]
             [motive-out (check Γ motive (PI (LIST entry-t) (H-O-CLOS 'n (lambda (_) (UNI)))))]
             [motive-val (go (val (ctx->env Γ) motive-out))]
             [base-out (check Γ base (do-ap motive-val (NIL)))]
             [step-out (check Γ
                              step
                              (ind-List-step-type motive-val entry-t))])
            (go `(the ,(read-back-norm
                   Γ
                   (THE (UNI)
                        (do-ap motive-val (val (ctx->env Γ) target-out))))
                 (ind-List ,target-out ,motive-out ,base-out ,step-out))))]
    ;adding synthesizing for ind-Vec
    ;note that it needs to be figured out what the type of the vec entries are, for now theres the
    ;assumption that the target has the form `(the A B)
    [`(ind-Vec ,n ,target ,motive ,base ,step)
     (go-on ([n-out (check Γ n (NAT))]
             [`(the ,target-t-t ,target-out-t) (synth Γ target)]
             [entry-t (go (match (val (ctx->env Γ) target-t-t) [(VEC E n) E]))]
             [target-out (go target-out-t)]
             [motive-out (check Γ motive (PI (NAT) (H-O-CLOS 'arg (lambda (arg) (PI (VEC entry-t arg) (H-O-CLOS 'n (lambda (_) (UNI))))))))]
             [motive-val (go (val (ctx->env Γ) motive-out))]
             [base-out (check Γ base (do-ap (do-ap motive-val (ZERO)) (VECNIL)))]
             [step-out (check Γ
                              step
                              (ind-Vec-step-type motive-val entry-t))])
            (go `(the ,(read-back-norm
                   Γ
                   (THE (UNI)
                        (do-ap (do-ap motive-val (val (ctx->env Γ) n-out)) (val (ctx->env Γ) target-out))))
                 (ind-Vec ,n-out ,target-out ,motive-out ,base-out ,step-out))))]
    [`(= ,A ,from ,to)
     (go-on ([`(the ,A-t ,A-temp) (synth Γ A)]
             [`(U ,n) (U-check Γ A-t)]
             [A-out (check A-temp (UNI (val (ctx->env Γ) n) ))]
             [A-val (go (val (ctx->env Γ) A))]
             [from-out (check Γ from A-val)]
             [to-out (check Γ to A-val)])
       (go `(the (U ,n) (= ,A-out ,from-out ,to-out))))]
    ;type is directly syntehsized for the motive, this feels a bit inneficient, but its necessary so it allows more complex statements
    ;would be better if it was also considered where i can synthesize the base and the to and take the max fo the two types
    ;or i can apply motive to the from and to and then synthesize a type for both and then take the max of the two
    [`(replace ,target ,motive ,base)
     (go-on ([`(the ,target-t ,target-out) (synth Γ target)])
       (match (val (ctx->env Γ) target-t)
         [(EQ A from to)
          (go-on ([`(,(or 'Π 'Pi) ((,k ,S)) ,M) (synth Γ motive)]
                  [`(U ,n) (U-check Γ M)]
                  [motive-out
                   (check Γ
                          motive
                          (PI A (H-O-CLOS 'x (lambda (x) (UNI (val (ctx->env Γ) n))))))]
                  [motive-v (go (val (ctx->env Γ) motive-out))]
                  [base-out (check Γ base (do-ap motive-v from))])
            (go `(the ,(read-back-norm Γ (THE (UNI (val (ctx->env Γ) n)) (do-ap motive-v to)))
                      (replace ,target-out ,motive-out ,base-out))))]
         [non-EQ
          (stop target (format "Expected =, but type is ~a" non-EQ))]))]
    ;need to take the max of the types U, Uof(A) and Uof(B)
    [`(,(or 'Π 'Pi) ((,x ,A)) ,B)
     
     (go-on ([`(the ,A-type ,A-temp) (synth Γ A)]
             [`(U ,n) (U-check Γ A-type)]
             [A-out (check Γ A (UNI (val (ctx->env Γ) n)))]
             
             [`(the ,B-type ,B-temp) (synth (extend-ctx Γ x (val (ctx->env Γ) A-out)) B)]
             [`(U ,k) (U-check Γ B-type)]
             ;this next line is incorrect, checking if B is the same type level as A doesn't make sense
             ;[B-out (check (extend-ctx Γ x (val (ctx->env Γ) A-out)) B (UNI (check Γ A (UNI (val (ctx->env Γ) n)))))]
             )
            
       ;(go `(the (U ,(greater-Nat (cdr (cdr A-out)) (cdr (cdr B-out)))) (Π ((,x ,(car A-out))) ,(car B-out)))))]
    (go `(the (U ,(greater-Nat n k)) (Π ((,x ,A-temp)) ,B-temp))))]

     ;(go-on ([A-out (check Γ A (UNI (ZERO)) #t)]
     ;        [B-out (check (extend-ctx Γ x (val (ctx->env Γ) A-out)) B (UNI (ZERO)) #t)])
     ;  (go `(the (U ,(greater-Nat (cdr (cdr A-out)) (cdr (cdr B-out)))) (Π ((,x ,(car A-out))) ,(car B-out)))))]
    ['Trivial (go '(the (U zero) Trivial))]
    ['Absurd (go '(the (U zero) Absurd))]
    [`(ind-Absurd ,target ,motive)
     (go-on ([target-out (check Γ target (ABSURD))]
             [`(the ,A ,B) (synth Γ motive)]
             [`(U ,n) (U-check Γ A)]
             ;this next line is probably redundant, try and remove some useless stuff
             [motive-out (check Γ motive (UNI (val (ctx->env Γ) n)))])
       (go `(the ,motive-out (ind-Absurd ,target-out ,motive-out))))]
    ['Atom (go '(the (U zero) Atom))]
    [`(,rator ,rand)
     (go-on ([`(the (,(or 'Π 'Pi) ((,k ,S)) ,M) ,rator-out) (synth Γ rator)]
             ;thiss line 893 is a bit inneficient considering line 892
             [`(the ,rator-t ,rator-out) (synth Γ rator)]
             [`(the ,rator-t-t ,temp) (synth Γ rator-t)]
             [`(U ,v) (U-check Γ rator-t-t)]
             [`(the ,M-type ,M-temp) (synth (extend-ctx Γ k (val (ctx->env Γ) S)) M)]
             [`(U ,g) (U-check Γ M-type)])
       ;once again readbacknorm doesn't care about universe type, so im going to fix it to be UNI ZERO
       (match (val (ctx->env Γ) rator-t)
         [(PI A B)
          (go-on ([rand-out (check Γ rand A)])
            (go `(the ,(read-back-norm Γ
                                       ;(THE (UNI (val (ctx->env Γ) g))
                                        (THE (UNI (ZERO))
                                            (val-of-closure B
                                                            (val (ctx->env Γ)
                                                                 rand-out))))
                      (,rator-out ,rand-out))))]
         [non-PI (stop rator
                       (format "Expected a Π type, but this is a ~a"
                               (read-back-norm Γ (THE (UNI (val (ctx->env Γ) v)) non-PI))))]))]
    ;i filled the following section in with UNI zeroes because it doesn't seem like the readbacknorm function actually cares about UNI level
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
    [(k k) k]))





; Γ : context?
; e : expr?
; t : value?

;i can add some subsumption here
;if bool is true, that means you want to check which universe it *is* an element of. returns a (cons (go whatever) `(U n))
;note that the synth call here might be a bit circular
(define (U-check Γ expr)
  (match expr
    [`(U ,n) (go `(U ,n))]
    [non-U (stop expr (format "Expected (U n) got ~v" (read-back-norm Γ (val (ctx->env Γ) (synth Γ expr) non-U))))]))

;once again read-back-norm doesn't seem to care about UNI type
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
  ;need to change U list
    [`(add1 ,n)
     (match t
       [(NAT)
        (go-on ([n-out (check Γ n (NAT))])
          (go `(add1 ,n-out)))]
       [non-NAT (stop e (format "Expected Nat, got ~v" (read-back-norm Γ (THE (UNI) non-NAT))))])]
    ;adding checking for nil and ::, but the output message is weird, need to fix the (List E) part
    ['nil
     (match t
       [(LIST E) (go 'nil)]
       [non-LIST (stop e (format "Expected (List E), got ~v"
                                (read-back-norm Γ (THE (UNI) non-LIST))))])]
    [`(:: ,hed ,tal)
     (match t
       [(LIST E)
        (go-on ([h-out (check Γ hed E)]
                [t-out (check Γ tal (LIST E))])
          (go `(:: ,h-out ,t-out)))]
       [non-LIST (stop e (format "Expected (List E), got ~v"
                                  (read-back-norm Γ (THE (UNI) non-LIST))))])]

    ;adding checking for vecnil and vec::, but the output message is weird, need to fix the (Vec E) part
    ['vecnil
     (match t
       [(VEC E (ZERO)) (go 'vecnil)]
       [non-VEC (stop e (format "Expected (Vec E zero), got ~v"
                                (read-back-norm Γ (THE (UNI) non-VEC))))])]
    [`(vec:: ,hed ,tal)
     (match t
       [(VEC E (ADD1 n))
        (go-on ([h-out (check Γ hed E)]
                [t-out (check Γ tal (VEC E n))])
          (go `(vec:: ,h-out ,t-out)))]
       [non-LIST (stop e (format "Expected (Vec E (add1 n)), got ~v"
                                   (read-back-norm Γ (THE (UNI) non-LIST))))])]

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
             ;the next line is for testing
             ;[`(the ,thing1 ,thing2) (synth Γ `(the chiedby zero))]
             [`(the ,t-of-t ,temp) (synth Γ t-out)]
             ;need to take the max of the two U_ns probably
             ;need to actually be checking if t-out is a *subtype* of t, not just alpha equivalent
             ;alpha equivalence is what convert does by default
             ;you should leave the alpha equivalence checker unchanged because some things do need to be precisely equal
             ;such as x and y in a (= A x y)
             [`(U ,n) (U-check Γ t-of-t)]
             ;[`(U (add1 (add1, n))) (U-check Γ t-of-t)]
             [`(the ,t-of-t2 ,temp2) (synth Γ (read-back-norm Γ (THE (UNI (ZERO)) t)))]
             [`(U ,n2) (U-check Γ t-of-t2)]
             ;I dont actually think that the subtype converter requires the type of the type, this is
             ;something that is relevant because some types dont actually have types: eg (Pi ((n Nat)) (U n))
             ;and as a result the synthesizer gives the type of (Pi ((n Nat)) (U n)) as something like (U (add1 n)) where n is a var
             ;this is obviously not viable, unless you created like some special var n, which allows this to have a type and like
             ;weird parameterizations, but more simply, we'll just say it doesn't have a type
             ;making it so that (Pi ((n Nat)) (U n)) is not a valid expression feels too restrictive. Its
             ;akin to how certain expressions in Pie don't have types
             [_ (subtype-convert Γ t (val (ctx->env Γ) t-out) t)])
             
       (go e-out))]))

; t : value?
; v1 : value?
; v2 : value?

;once again recall that readbacknorm doesn't care about uni type
;the onyl time v1 and v2 are not going to be types here is the (=...) statement
(define (convert Γ t v1 v2)
  (define e1 (read-back-norm Γ (THE t v1)))
  (define e2 (read-back-norm Γ (THE t v2)))
  (if (α-equiv? e1 e2)
      (go 'ok)
      (stop e1 (format "Expected to be the same ~v as ~v"
                       (read-back-norm Γ (THE (match t [(UNI n) (UNI (ADD1 n))]) t))
                       e2))))

;lvl here is not is a nat, could be neutral, not in (ADD1... form, its in (add1... form
(define (subtype-convert Γ lvl t1 t2)
  ;read-back-norm doesn't care about uni type
  ;(define e1 (read-back-norm Γ (THE t t1)))
  ;(define e2 (read-back-norm Γ (THE t t2)))
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


(run-program `() `((the (Pi((n Nat))(Vec Nat n)) (lambda(x)(ind-Nat (the Nat x)
                                                                (the (Pi ((k Nat)) U) (lambda(k) (Vec Nat k)))
                                                                (the (Vec Nat zero) vecnil)
                                                                (the (Pi ((nt Nat)) (Pi ((par (Vec Nat nt))) (Vec Nat (add1 nt))))
                                                                     (lambda(r) (lambda (s) (vec:: zero s)))))))))
;(trace run-program)
;(trace interact)
;(trace convert)
;(trace U-check)
(trace synth)
(trace check)
;(trace α-equiv?)
;(trace α-equiv-aux)
;(trace subtype?)
;(trace α-subtype-aux)
(trace val)
(trace greater-Nat)
;(trace subtype-convert)
;(trace read-back-norm)
;(run-program `() `((the (U (add1 (add1 zero))) (U zero))))
;(run-program `() `((the (U (add1 (add1 zero))) (U (add1 zero)))))
;(run-program `() `((the (Pi ((x Absurd)) (Pi ((y (U (add1 zero)))) y)) (lambda (x) (lambda (y) (ind-Absurd x y))))))
;(run-program `() `((define fn (the (Pi ((x Nat)) (Pi ((y (U (add1 zero)))) y)) (lambda (x) (lambda (y) Nat)))))) example of whats not allowed

;important notes:
;You can't write a proof for types like (Pi ((y (U (add1 zero)))) y), since y could be a (U zero), meaning that every statement can be proven

;(run-program `() `((define fn (the (Pi ((n (U (add1 (add1 zero))))) (U (add1 zero))) (lambda (x) Nat))) (fn (the (U (add1 (add1 zero))) (U (add1 zero))))))

;(run-program `() `((the (Sigma ((n (U (add1 (add1 zero))))) (U (add1 zero))) (cons (U zero) (U zero)))))
;(run-program `() `((the (Pi ((x Nat)) (U (add1 (add1 x)))) (lambda (x) (U (add1 x))))))


;(run-program `() `((the (U (add1(add1 zero)))
;                        (ind-Nat
;                                 (the Nat (add1 zero))
;                                 (the (Pi ((n Nat)) (U (add1 (add1 n)))) (lambda (x) (U (add1 x))))
;                                 (the (U (add1 zero)) (U zero))
;                                 (the (Pi ((n Nat)) (Pi ((k (U (add1 n)))) (U (add1 n)))))))))

;(run-program `() `((the (U (add1 (add1 zero)))
 ;                       (ind-Nat
 ;                                (the Nat (add1 zero))
;                                 (the (Pi ((n Nat)) (U (add1 (add1 n)))) (lambda (x) (U (add1 x))))
;                                 (the (U (add1 zero)) (U zero))
;                                 (the (Pi ((n Nat)) (Pi ((k (U (add1 n)))) (U (add1 (add1 n))))) (lambda (x) (lambda (y) (U (add1 x)))))))))

;(run-program `() `((define fn (the (Pi ((n Nat)) (U (add1 n)))
;                        (lambda(n)(ind-Nat
;                                 (the Nat n)
;                                 (the (Pi ((n Nat)) (U (add1 (add1 n))))
;                                      (lambda (x) (U (add1 x))))
;                                 (the (U (add1 zero))
;                                      (U zero))
;                                 (the (Pi ((n Nat)) (Pi ((k (U (add1 n)))) (U (add1 (add1 n)))))
;                                      (lambda (x) (lambda (y) (U (add1 x)))))))))
;                   (fn (the Nat (add1 zero)))))

;(run-program `() `((define fn (the (Pi ((n Nat)) (U (add1 (ind-Nat
;                                 (the Nat n)
 ;                                (the (Pi ((n Nat)) (U (add1 (add1 n))))
;                                      (lambda (x) (U (add1 x))))
;                                 (the (U (add1 zero))
;                                      (U zero))
;                                 (the (Pi ((n Nat)) (Pi ((k (U (add1 n)))) (U (add1 (add1 n)))))
;                                      (lambda (x) (lambda (y) (U (add1 x)))))))))
;                        (lambda(n)(ind-Nat
;                                 (the Nat n)
;                                 (the (Pi ((n Nat)) (U (add1 (add1 n))))
;                                      (lambda (x) (U (add1 x))))
;                                 (the (U (add1 zero))
;                                      (U zero))
;                                 (the (Pi ((n Nat)) (Pi ((k (U (add1 n)))) (U (add1 (add1 n)))))
;                                      (lambda (x) (lambda (y) (U (add1 x)))))))))
                   ;(fn (the Nat (add1 zero)))
;                   ))
                                      ;(lambda (x) (lambda (y) (U (add1 x)))))))))))

;(run-program `() `((the (Pi ((n Nat)) (Pi ((y (U n))) Nat)) (lambda(x)(lambda(y) zero)))))

;(go '(the (Π ((n Nat)) (U (add1 (add1 n)))) (λ (x) (U (add1 x)))))
