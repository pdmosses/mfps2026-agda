# Booleans

The McCarthy conditional operation `β ⟶ δ₁ , δ₂` extends the usual ternary
conditional choice to domains. It returns `⊥` whenever its first argument is `⊥`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Notation.Flat.Booleans where

  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Flat
  open import Data.Bool.Base public using (Bool; false; true; if_then_else_)

  Bool⊥ = Bool +⊥
  _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫    -- β ⟶ δ₁ , δ₂ is conditional choice
  _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂) ♯  
--"hide"
  infixr 20 _⟶_,_
--"/hide"
```
This module also defines `Eq A` for use as an instance parameter,
restricting operation definitions to types `A` such that `_==_ : A → A → Bool`,
and postulates a `Bool⊥`-valued operation `δ₁ ==⊥ δ₂` on `A +⊥`.
```agda
--"hide"
  record Eq (A : Set) : Set where field _==_ : A → A → Bool
  open Eq {{...}} public
  postulate
    _==⊥_ : {{Eq A}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
    -- δ₁ ==⊥ δ₂ is ⊥ when either operand is ⊥
    instance eqBool : Eq Bool
--"/hide"
```
