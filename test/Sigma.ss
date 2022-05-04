(import (only (chezscheme) record-case))

(define (fst) (lambda (a) (record-case a ((_,_) (b c) b))))

(define (snd) (lambda (a) (record-case a ((_,_) (b c) c))))

(define (_\x2C;_) (lambda (a) (lambda (b) (list '_,_ a
b))))