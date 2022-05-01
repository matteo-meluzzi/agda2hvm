(import (only (chezscheme) record-case))

(define (Node) (lambda (a) (lambda (b) (list 'Node a
b))))

(define (Leaf) (lambda (a) (list 'Leaf a)))

(define (gen) (lambda (a) (if (= 0 a) ((Leaf) 1)
(let ((b (- a 1))) (((Node) ((gen) b)) ((gen) b))))))

(define (sun) (lambda (a) (record-case a ((Node) (b c) (+ ((sun) b) ((sun) c)))
((Leaf) (d) 1))))

(define (main) ((sun) ((gen) 22)))