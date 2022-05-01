(import (only (chezscheme) record-case))

(define (plus3) (lambda (a) (+ 3 a)))

(define (pred) (lambda (a) (if (= 0 a) 0
(- a 1))))

(define (test1) ((pred) (+ 1 ((pred) ((plus3) 40)))))

(define (twice) (lambda (a) (* 2 a)))

(define (pow2) (lambda (a) (if (= 0 a) 1
(let ((b (- a 1))) ((twice) ((pow2) b))))))

(define (consume) (lambda (a) (if (= 0 a) 0
(let ((b (- a 1))) ((consume) b)))))

(define (fac) (lambda (a) (if (= 0 a) 1
(let ((b (- a 1))) (* a ((fac) b))))))

(define (fib) (lambda (a) (if (= 0 a) 0
(if (= 1 a) 1
(let ((b (- a 2))) (+ ((fib) (- a 1)) ((fib) b)))))))

(define 
  (if_then_else_)
  (lambda (a) (lambda (b) (lambda (c) (lambda (d) (record-case b ((false) () d)
((true) () c)))))))

(define (ifte) (((((if_then_else_) (list)) (true)) 1) 0))

(define (test2) ((consume) ((pow2) 24)))

(define (main) ((fib) 40))