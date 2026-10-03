# Flat Domains

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Properties.Flat where
  open import Notation.Domains
  open import Notation.Flat public
  open import Agda.Builtin.Equality public using (_≡_; refl)
  open import Agda.Builtin.Equality.Rewrite using ()

  variable f : A → ⟪ D ⟫; a′ : A
  postulate
    elim-♯-↑  : (f ♯) (↑ a′)  ≡ f a′
    elim-♯-⊥  : (f ♯) ⊥      ≡ ⊥
  {-# REWRITE elim-♯-↑ #-}
```
