(import (only (chezscheme) record-case))

(define (True) (list 'True))

(define (False) (list 'False))

(define (Nil) (list 'Nil))

(define (Cons) (lambda (a) (lambda (b) (list 'Cons a
b))))

(define (main) (((Cons) (True)) (((Cons) (False)) (Nil))))