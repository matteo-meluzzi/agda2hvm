(import (only (chezscheme) record-case))

(define (A) (begin (display "encountered axiom: A\n") (exit 1)))

(define (true) (list 'true))

(define (false) (list 'false))

(define (id) (lambda (a) a))

(define (id2) (lambda (a) (lambda (b) (lambda (c) a))))

(define (matteo) (lambda (a) (lambda (b) (a b))))

(define (luca) ((matteo) (lambda (a) a)))

(define (nikos) ((luca) (true)))

(define 
  (xor)
  (lambda 
    (a)
    (lambda 
      (b)
      (record-case a ((true) () (record-case b ((true) () (false))
((false) () a)))
((false) () b)))))

(define (main) (nikos))