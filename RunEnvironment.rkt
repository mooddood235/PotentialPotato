#lang pie

(claim x
  (-> Nat Nat))

(define x (the (-> Nat Nat) (lambda (x) x)))

x