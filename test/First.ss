(import (only (chezscheme) record-case))

(define (True) (list 'True))

(define (False) (list 'False))

(define (Z) (list 'Z))

(define (S) (lambda (a) (list 'S a)))

(define (Nil) (list 'Nil))

(define (Cons) (lambda (a) (lambda (b) (list 'Cons a
b))))

(define (P) (lambda (a) (lambda (b) (list 'P a
b))))

(define (Matteo) (list 'Matteo))

(define (Nikos) (list 'Nikos))

(define (Luca) (list 'Luca))

(define (Andrei) (list 'Andrei))

(define 
  (friend)
  (lambda 
    (a)
    (record-case a ((Matteo) () (False))
((Nikos) () (True))
((Luca) () (True))
((Andrei) () (True)))))

(define (not) (lambda (a) (record-case a ((True) () (False))
((False) () (True)))))

(define (main) (((P) (True)) (False)))