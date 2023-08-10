#lang racket

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

(provide desugar)