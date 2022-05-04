(import (only (chezscheme) record-case))

(define (putStrLn) (begin (display "encountered axiom: putStrLn\n") (exit 1)))

(define (main) ((putStrLn) (begin (display "not yet supported: String literals\n") (exit 1))))