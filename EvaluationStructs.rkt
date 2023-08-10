#lang racket

; env : Env
; var : symbol?
; body : any/c
(struct CLOS (env var body) #:transparent)

(struct ZERO () #:transparent)

(struct INFTY () #:transparent)

; pred : value
(struct ADD1 (pred) #:transparent)

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

(struct LIST (entry-type) #:transparent)
(struct NIL () #:transparent)
(struct CONCAT:: (head tail) #:transparent)


(struct VEC (entry-type len) #:transparent)
(struct VECNIL () #:transparent)
(struct VCAT:: (head tail) #:transparent)

; type : value?
; neutral : neutral?
(struct NEU (type neutral) #:transparent)

; x : symbol?
; fun : (-> value ? value?)
(struct H-O-CLOS (x fun) #:transparent)

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


(struct N-ind-List (target motive base step) #:transparent)



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

(provide (all-defined-out))