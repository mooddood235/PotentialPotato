#lang racket

(require "EvaluationStructs.rkt")

; c : closure?
(define (closure-name c)
  (match c
    [(CLOS _ x _) x]
    [(H-O-CLOS x _) x]))

(provide (all-defined-out))