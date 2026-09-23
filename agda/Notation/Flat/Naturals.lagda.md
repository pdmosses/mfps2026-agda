# Naturals

Agda allows decimal notation for natural numbers, as well as unary notation
using `zero` and `suc`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Notation.Flat.Naturals where
  
  open import Notation.Flat
  open import Notation.Flat.Booleans
  open import Agda.Builtin.Nat public
    using (Nat; suc; _+_; _-_) renaming (_==_ to _==ᴺ_)

  Nat⊥ = Nat +⊥

  postulate 
    instance eqNat : Eq Nat
```
