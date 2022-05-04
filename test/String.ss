(import (only (chezscheme) record-case))

(define (String) (begin (display "encountered axiom: String\n") (exit 1)))

(define 
  (primStringUncons)
  (begin (display "encountered axiom: primStringUncons\n") (exit 1)))

(define 
  (primStringToList)
  (begin (display "encountered axiom: primStringToList\n") (exit 1)))

(define 
  (primStringFromList)
  (begin (display "encountered axiom: primStringFromList\n") (exit 1)))

(define 
  (primStringAppend)
  (begin (display "encountered axiom: primStringAppend\n") (exit 1)))

(define 
  (primStringEquality)
  (begin (display "encountered axiom: primStringEquality\n") (exit 1)))

(define (primShowChar) (begin (display "encountered axiom: primShowChar\n") (exit 1)))

(define (primShowString) (begin (display "encountered axiom: primShowString\n") (exit 1)))

(define (primShowNat) (begin (display "encountered axiom: primShowNat\n") (exit 1)))