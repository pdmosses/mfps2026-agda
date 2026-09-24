```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Properties.Recursion where

  open import Notation.Domains
  open import Notation.Recursion using (_≅_; unfold; fold) public
  open import Agda.Builtin.Equality public using (_≡_; refl)
  open import Agda.Builtin.Equality.Rewrite using ()

  postulate
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}
```
A rule for `fold (unfold d) ≡ d` could be added, but it is not needed for the current illustrative tests.
