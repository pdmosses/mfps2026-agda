# Scm Tests

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Tests.Scm where
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

```
Check `ℰ⟦ ⦅if E ␣ E₁ ␣ E₂ ⦆ ⟧ ρ κ`:
```agda
  check-if-t : 
    ℰ⟦ ⦅if con #t ␣ con (int (+ 1)) ␣ con (int (+ 2)) ⦆ ⟧ ρ κ ≡ κ (↑ (+ 1) in⊥ 𝐄)
  check-if-t = refl

  check-if-f : 
    ℰ⟦ ⦅if con #f ␣ con (int (+ 1)) ␣ con (int (+ 2)) ⦆ ⟧ ρ κ ≡ κ (↑ (+ 2) in⊥ 𝐄)
  check-if-f = refl

  check-if-0 : 
    ℰ⟦ ⦅if con (int (+ 0)) ␣ con (int (+ 1)) ␣ con (int (+ 2)) ⦆ ⟧ ρ κ ≡ κ (↑ (+ 1) in⊥ 𝐄)
  check-if-0 = refl

  check-if-1 : 
    ℰ⟦ ⦅if con (int (+ 1)) ␣ con (int (+ 1)) ␣ con (int (+ 2)) ⦆ ⟧ ρ κ ≡ κ (↑ (+ 1) in⊥ 𝐄)
  check-if-1 = refl

  check-if-lambda : 
    ℰ⟦ ⦅if ⦅lambda I ␣ ide I ⦆ ␣ con (int (+ 1)) ␣ con (int (+ 2)) ⦆ ⟧ ρ κ ≡ κ (↑ (+ 1) in⊥ 𝐄)
  check-if-lambda = refl

  check-if-unspecified : 
    ℰ⟦ ⦅if ⦅set! I ␣ con #f ⦆ ␣ con (int (+ 1)) ␣ con (int (+ 2)) ⦆ ⟧ ρ κ σ ≡ κ (↑ (+ 1) in⊥ 𝐄) _
  check-if-unspecified = refl

```
Check `ℰ⟦ ide I ⟧ ρ κ`: **FAILED TO RESOLVE INSTANCE ARGUMENTS FOR `_[_/_]`!**
```agda
  -- check-ide :
  --   ℰ⟦ ide I ⟧ (ρ [ α / I ]) κ (σ [ ε / α ]) ≡ κ ε (σ [ ε / α ])
  -- check-ide = refl

```
(To be continued...)
