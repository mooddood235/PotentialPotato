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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ρ : environment?
; e : expression?
;(define (val ρ e)
 ; (match e
  ;  [`(λ (,x) ,b)
   ;  (CLOS ρ x b)]
    ;[x #:when (symbol? x)
     ;(let ((xv (assv x ρ)))
      ; (if xv
       ;    (cdr xv)
        ;   (error 'val "Unknown variable ~a" x)))]
;    [`(,rator ,rand)
 ;    (do-ap (val ρ rator) (val ρ rand))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; fun : value?
; arg : value?
;(define (do-ap fun arg)
 ; (match fun
  ;  [(CLOS ρ x b)
  ;   (val (extend ρ x arg) b)]
    ; If the argument is neutral, construct a bigger neutral expression.
   ; [neutral-fun
    ; (N-ap fun arg)]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ρ : (listof (pair symbol? value?))
; exprs : (listof expression?)
;(define (run-program ρ exprs)
 ; (match exprs
;    [(list) (void)]
;    [(list `(define ,x ,e) rest ...)
;     (let ([v (val ρ e)])
;       (run-program (extend ρ x v) rest))]
;    [(list e rest ...)
;     (displayln (norm ρ e))
;     (run-program ρ rest)]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; used-names : (listof symbol?)
; v : value?
;(define (read-back used-names v)
;  (match v
;    [(CLOS ρ x body)
;     (let* ((y (freshen used-names x))
;            (neutral-y (N-var y)))
;       `(λ (,y)
;          ,(read-back (cons y used-names)
;                      (val (extend ρ x neutral-y) body))))]
;    [(N-var x) x]
;    [(N-ap rator rand)
;     `(,(read-back used-names rator) ,(read-back used-names rand))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
; e : expression?
(define (synth Γ e)
  (match e
    ; Type annotations
    [`(the ,t ,e2)
     (if (not (type? t))
         (stop e (format "Invalid type ~a" t))
         (go-on ([_ (check Γ e2 t)])
           (go t)))]
    ; Recursion on Nat
    [`(rec ,type ,target ,base ,step)
     (go-on ([target-t (synth Γ target)]
             [_ (if (type=? target-t 'Nat)
                    (go 'ok)
                    (stop target (format "Expected Nat, got ~v"
                                         target-t)))]
             [_ (check Γ base type)]
             [_ (check Γ step `(→ Nat (→ ,type ,type)))])
       (go type))]
    [x #:when (and (symbol? x)
                   (not (memv x '(the rec λ zero add1))))
     (match (assv x Γ)
       [#f (stop x "Variable not found")]
       [(cons _ t) (go t)])]
    [`(,rator ,rand)
     (go-on ([rator-t (synth Γ rator)])
       (match rator-t
         [`(→ ,A ,B)
          (go-on ([_ (check Γ rand A)])
            (go B))]
         [else (stop rator (format "Not a function type: ~v"
                                   rator-t))]))]))
; Γ : context?
; e : expression?
; t : type?

(define (check Γ e t)
  (match e
    ['zero
     (if (type=? t 'Nat)
         (go 'ok)
         (stop e (format "Tried to use ~v for zero" t)))]
    [`(add1 ,n)
     (if (type=? t 'Nat)
         (go-on ([_ (check Γ n 'Nat)])
           (go 'ok))
         (stop e (format "Tried to use ~v for add1" t)))]
    [`(λ (,x) ,b)
     (match t
       [`(→ ,A ,B)
        (go-on ([_ (check (extend Γ x A) b B)])
          (go 'ok))]
       [non-arrow
        (stop e (format "Instead of → type, got ~a" non-arrow))])]
    [other
     (go-on ([t2 (synth Γ e)])
       (if (type=? t t2)
           (go 'ok)
           (stop e
                 (format "Synthesized type ~v where type ~v was expected"
                         t2
                         t))))]))

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

; p : environment
; e : expression
;(define (val ρ e)
;  (match e
;    [`(the ,type ,expr)
;     (val ρ expr)]
;    ['zero (ZERO)]
;    [`(add1 ,n) (ADD1 (val ρ n))]
;    [x #:when (and (symbol? x)
;                   (not (memv x '(the zero add1 λ rec))))
;     (cdr (assv x ρ))]
;    [`(λ (,x) ,b)
;     (CLOS ρ x b)]
;    [`(rec ,type ,target ,base ,step)
;     (do-rec type (val ρ target) (val ρ base) (val ρ step))]
;    [`(,rator ,rand)
;     (do-ap (val ρ rator) (val ρ rand))]))


; fun : value
; arg : value
;(define (do-ap fun arg)
;  (match fun
;    [(CLOS ρ x e)
;     (val (extend ρ x arg) e)]
;    [(NEU `(→ ,A ,B) ne)
;     (NEU B (N-ap ne (THE A arg)))]))

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

; used-names : (listof symbol?)
; ne : neutral?
;(define (read-back-neutral used-names ne)
;  (match ne
;    [(N-var x) x]
;    [(N-ap fun (THE arg-type arg))
;     `(,(read-back-neutral used-names fun)
;       ,(read-back used-names arg-type arg))]
;    [(N-rec type target (THE base-type base) (THE step-type step))
;     `(rec ,type
;        ,(read-back-neutral used-names target)
;        ,(read-back used-names base-type base)
;        ,(read-back used-names step-type step))]))


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

; Δ : definitions?
; prog : (listof (or/c (list 'define symbol? expression?)
;              expression?))

(define (run-program Δ prog)
  (match prog
    ['() (go Δ)]
    [(cons `(define ,x ,e) rest)
     (go-on ([type (synth (defs->ctx Δ) e)])
       (run-program (extend Δ x (def type (val (defs->env Δ) e)))
                    rest))]
    [(cons e rest)
     (let ([Γ (defs->ctx Δ)]
           [ρ (defs->env Δ)])
       (go-on ([type (synth Γ e)])
         (let ([v (val ρ e)])
           (begin
             (printf "(the ~a\n  ~a)\n"
                     type
                     (read-back (map car Γ) type v))
             (run-program Δ rest)))))]))

(define keywords
  (list 'define
        'U
        'Nat 'zero 'add1 'ind-Nat
        'Σ 'Sigma 'cons 'car 'cdr
        'Π 'Pi 'λ 'lambda
        '= 'same 'replace
        'Trivial 'sole
        'Absurd 'ind-Absurd
        'Atom 'quote
        'the))

; x : keyword?
(define (keyword? x)
  (if (memv x keywords)
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

; target : neutral?
; motive : normal?
; base : normal?
(struct N-replace (target motive base) #:transparent)

; target : neutral?
; motive : normal?
(struct N-ind-Absurd (target motive) #:transparent)

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

; p : environment?
; e : expression?
(define (val ρ e)
  (match e
    [`(the ,type ,expr)
     (val ρ expr)]
    ['U (UNI)]
    [`(Π ((,x ,A)) ,B)
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
    [(N-replace ne motive base)
     `(replace ,(read-back-neutral Γ ne)
               ,(read-back-norm Γ motive)
               ,(read-back-norm Γ base))]
    [(N-ind-Absurd ne motive)
     `(ind-Absurd (the Absurd ,(read-back-neutral Γ ne))
                  ,(read-back-norm Γ motive))]))