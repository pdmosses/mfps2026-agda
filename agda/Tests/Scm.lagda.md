# Scm Tests

The following tests check that the denotations of some expressions
in the abstract syntax of the PCF language compute the expected values
when applied to an arbitrary environment `ρ` and continuation `κ`.

Further tests are to be developed, together with properties of operations
on tuples and sequences.

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

Due to potential non-injectivity of the postulated operation `⟪_⟫`,
the definitions of `_[_/_]` and `_[_/_]⊥` need to be instantiated at `D∞`
for the type-checker to resolve the `lookup-ide` test.

*This isn't yet working...*

```agda
  _[_/_]𝐋 : {{Eq A}} → ⟪ 𝐔 →ᶜ 𝐋 →ᶜ Ide →ˢ 𝐔 ⟫
  ρ [ α / I ]𝐋 = λ I′ → if I == I′ then α else ρ I′

  -- _[_/_]⊥𝐄 : {{Eq Loc}} → ⟪ 𝐒 →ᶜ 𝐄 →ᶜ 𝐋 →ᶜ 𝐒 ⟫
  -- _[_/_]⊥𝐄 {{eqL}} σ ε α = λ α′ → (α ==⊥ α′) ⟶ ε , σ α′

  -- lookup-ide :
  --   ℰ⟦ ide I ⟧ (ρ [ α / I ]𝐋) κ (σ [ ε / α ]⊥𝐄) ≡ κ ε (σ [ ε / α ]⊥𝐄)
  -- lookup-ide = refl

```
(To be continued...)
