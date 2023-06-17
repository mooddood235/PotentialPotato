#lang racket

; env : Env
; var : symbol?
; body : any/c
(struct CLOS (env var body) #:transparent)

; ρ : environment?
; x : symbol?
; v : value?
(define (extend p x v)
  (cons (cons x v) p))

; ρ : environment?
; e : expression?
(define (val ρ e)
  (match e
    [`(λ (,x) ,b)
     (CLOS ρ x b)]
    [x #:when (symbol? x)
     (let ((xv (assv x ρ)))
       (if xv
           (cdr xv)
           (error 'val "Unknown variable ~a" x)))]
    [`(,rator ,rand)
     (do-ap (val ρ rator) (val ρ rand))]))


; fun : value?
; arg : value?
(define (do-ap fun arg)
  (match fun
    [(CLOS ρ x b)
     (val (extend ρ x arg) b)]
    ; If the argument is neutral, construct a bigger neutral expression.
    [neutral-fun
     (N-ap fun arg)]))

; exprs : (listof expression?)
(define (run-program ρ exprs)
  (match exprs
    ['() (void)]
    [(cons `(define ,x ,e) rest)
     (let ([v (val ρ e)])
       (run-program (extend ρ x v) rest))]
    [(cons e rest)
     (displayln (val ρ e))
     (run-program ρ rest)]))


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

; name : symbol?
(struct N-var (name))

;rator : neutral?
;rand : value?
(struct N-ap (rator rand))

; used-names : (listof symbol?)
; v : value?
(define (read-back used-names v)
  (match v
    [(CLOS ρ x body)
     (let* ((y (freshen used-names x))
            (neutral-y (N-var y)))
       `(λ (,y)
          ,(read-back (cons y used-names)
                      (val (extend ρ x neutral-y) body))))]
    [(N-var x) x]
    [(N-ap rator rand)
     `(,(read-back used-names rator) ,(read-back used-names rand))]))

(define (norm ρ e)
  (read-back '() (val ρ e)))



