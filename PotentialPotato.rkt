#lang racket

(require "ErrorHandling.rkt")
(require "TypeChecking.rkt")
(require "Desugar.rkt")
(require "GeneralUtils.rkt")
(require "Evaluation.rkt")
(require "EvaluationStructs.rkt")

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


(define (run inputs)
  (run-program `() inputs))


(provide run-program run)
                                                  