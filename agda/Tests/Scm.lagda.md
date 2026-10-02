# Scm Tests

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Tests.Scm where
--"hide"
  open import Examples.Scm.Abstract-Syntax
  open import Examples.Scm.Domain-Equations
  open import Examples.Scm.Auxiliary-Functions
  open import Examples.Scm.Semantic-Functions

  open import Properties.Domains
  open import Properties.Functions
  open import Properties.Flat
  open import Properties.Flat.Booleans
  open import Properties.Sums
  open import Properties.Products.Sequences
  open import Properties.Updates
--"/hide"

  check-sum : {β : ⟪ 𝐓 ⟫} → (β in⊥ 𝐄) ∈⊥ 𝐓 ≡ ↑ true
  check-sum = refl
```