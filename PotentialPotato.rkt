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

; clos : value?
; arg : value?
(define (do-ap clos arg)
  (match clos
    [(CLOS ρ x b)
     (val (extend ρ x arg) b)]))



