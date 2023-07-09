#lang pie

(claim identity
  (-> Nat Nat))

(define identity
  (lambda (x) x))

(add1 identity)