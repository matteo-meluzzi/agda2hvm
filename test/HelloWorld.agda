{-# OPTIONS --guardedness #-}

module HelloWorld where

open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import IO
open import Function.Base using (_$_)

main : Main
main = run $ putStrLn "Hello, World!"
