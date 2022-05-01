(import (only (chezscheme) record-case))

(define (zero) (list 'zero))

(define (suc) (lambda (a) (list 'suc a)))

(define (_+_) (begin (display "encountered axiom: _+_\n") (exit 1)))

(define (_-_) (begin (display "encountered axiom: _-_\n") (exit 1)))

(define (_*_) (begin (display "encountered axiom: _*_\n") (exit 1)))

(define (_==_) (begin (display "encountered axiom: _==_\n") (exit 1)))

(define (_<_) (begin (display "encountered axiom: _<_\n") (exit 1)))

(define (div-helper) (begin (display "encountered axiom: div-helper\n") (exit 1)))

(define (mod-helper) (begin (display "encountered axiom: mod-helper\n") (exit 1)))