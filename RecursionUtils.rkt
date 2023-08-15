#lang racket
(require "GeneralUtils.rkt")
(require "ErrorHandling.rkt")

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
    ;[`(,(or 'λ 'lambda) (,x) ,b) (check-recursive-form b)]
    [else
     (stop e "Recursive functions must be of the form (λ (e) (match A B e ...))")]))

(provide (all-defined-out))
                        
