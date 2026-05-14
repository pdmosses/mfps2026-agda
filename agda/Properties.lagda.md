# Postulated Properties

This module declares some properties of the conventional notation for
Scott domains and the associated functions on their carrier sets.
Postulated equivalences between terms are used for testing denotations of
terms; adding them as rewrite rules allows implicit use in proofs.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Properties where
--"hide"

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite using ()
open import Agda.Builtin.Nat public using (Nat) renaming (_==_ to _==ᴺ_) 
import Notation
open Notation using (A; B; C)

module Domains where
  open Notation.Domains using (Domain; ⟪_⟫; ⊥; 𝟙; D; E; F) public
open Domains public
--"/hide"

module Functions where
--"hide"
  open Notation.Functions using (_→ᶜ_; dom-cts; _→ˢ_; set-cts; fix) public
--"/hide"
  postulate
    apply-fix : {φ : ⟪ D →ᶜ D ⟫} → fix φ ≡ φ (fix φ)
    -- apply-fix{φ} unfolds fix φ once
  {-# REWRITE apply-fix #-}
--"hide"
open Functions public
--"/hide"

module Recursion where
--"hide"
  open Notation.Recursion using (_≅_; unfold; fold) public
--"/hide"
  postulate
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}

module Flat where
--"hide"
  open Notation.Flat using (_+⊥; ↑; _♯) public

  variable f : A → ⟪ D ⟫; a′ : A
--"/hide"
  postulate
    elim-♯-↑  : (f ♯) (↑ a′)  ≡ f a′
    elim-♯-⊥  : (f ♯) ⊥      ≡ ⊥
  {-# REWRITE elim-♯-↑ elim-♯-⊥ #-} 
--"hide"
  module Booleans where

    open Notation.Flat.Booleans using (Bool⊥; _⟶_,_; Eq; _==⊥_; eqBool) public
--"/hide"

  module Naturals where
--"hide"
    open Notation.Flat.Naturals using (Nat⊥; eqNat) public
    open Booleans

    variable n₁ n₂ : Nat
--"/hide"
    postulate
      elim-==⊥ : (↑ n₁ ==⊥ ↑ n₂) ≡ ↑ (n₁ ==ᴺ n₂)
    {-# REWRITE elim-==⊥ #-} 

module Sums where
--"hide"
  open Notation.Sums using (_+_; inj₁; inj₂; [_,_]) public

  variable φ : ⟪ D →ᶜ F ⟫; ψ : ⟪ E →ᶜ F ⟫; δ : ⟪ D ⟫; ε : ⟪ E ⟫
--"/hide"
  postulate
    elim-inj₁  :  [ φ , ψ ] (inj₁ δ)  ≡  φ δ
    elim-inj₂  :  [ φ , ψ ] (inj₂ ε)  ≡  ψ ε
    elim-[]-⊥  :  [ φ , ψ ] ⊥         ≡  ⊥
  {-# REWRITE elim-inj₁ elim-inj₂ #-} 
--"hide"
  open Notation.Sums using (n; _≳_↦_; _in⊥_; _|⊥_; _∈⊥_) public
  open Flat
  open Flat.Booleans
  open Flat.Naturals

  open import Relation.Binary.PropositionalEquality.Core using (_≢_)
  variable D′ : Domain; n′ : Nat
--"/hide"

  postulate
    elim-∈⊥    :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  (δ in⊥ E) ∈⊥ D′ ≡ ↑ (n ==ᴺ n′)
    elim-|⊥    :  {{_ : E ≳ n ↦ D}} → (δ : ⟪ D ⟫) → (δ in⊥ E) |⊥ D ≡ δ
    elim-∈⊥-⊥  :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  {n ≢ n′} → (δ in⊥ E) |⊥ D′ ≡ ⊥
  {-# REWRITE elim-∈⊥ elim-|⊥ #-} 

module Products where
--"hide"
  open Notation.Products using (_×_; _,_; _↓₁; _↓₂) public

  variable δ : ⟪ D ⟫; ε : ⟪ E ⟫
--"/hide"
  postulate
    elim-↓₁  :  ( δ , ε ) ↓₁  ≡  δ
    elim-↓₂  :  ( δ , ε ) ↓₂  ≡  ε
  {-# REWRITE elim-↓₁ elim-↓₂ #-} 
--"hide"
  module Tuples where
    open Notation.Products.Tuples using (_^_) public

  module Sequences where
    open Notation.Products.Sequences using (n; _⋆; ⟨⟩; ⟨_⟩; #; _§_; _↓_; _†_) public

module Updates where
  open Notation.Updates using (_[_/_]; _[_/_]⊥; _[_←_]) public
--"/hide"
```