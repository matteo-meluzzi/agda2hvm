(import (only (chezscheme) record-case))

(define (just) (lambda (a) (list 'just a)))

(define (nothing) (list 'nothing))