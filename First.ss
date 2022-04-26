(import (only (chezscheme) record-case))

(define (true) (list 'true))

(define (false) (list 'false))

(define (id) (lambda (a) (lambda (b) b)))

(define (id2) (lambda (a) (lambda (b) (lambda (c) (lambda (d) b)))))

(define (matteo) (lambda (a) (lambda (b) (a b))))

(define (luca) ((matteo) (lambda (a) a)))

(define (nikos) ((luca) (true)))