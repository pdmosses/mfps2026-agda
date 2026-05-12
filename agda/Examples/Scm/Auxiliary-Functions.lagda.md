# Auxiliary Functions

The $\lambda$-notation in the Agda definitions of auxiliary functions for Scm
corresponds closely to that in its conventional denotational semantics [(Mosses2025CSE)].
The main difference is the explicit application here of the function `↑` to inject
elements of sets into the carriers of flat domains, cf. the definition of `truish` below.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Examples.Scm.Auxiliary-Functions where
--"hide"

open import Examples.Scm.Abstract-Syntax
open import Examples.Scm.Domain-Equations
import Notation
open Notation.Domains using (⟪_⟫; ⊥)
open Notation.Functions using (_→ᶜ_; fix)
open Notation.Flat using (↑)
open Notation.Flat.Booleans using (_⟶_,_; Eq; _==⊥_; true; false)
open Notation.Sums using (_in⊥_; _∈⊥_; _|⊥_)
open Notation.Products using (_,_; _↓₁; _↓₂)
open Notation.Products.Sequences using (⟨_⟩; #; _↓_; _†_)
open Notation.Updates using (_[_/_]⊥)

postulate instance
  eqL   : Eq Loc
  eqM   : Eq Misc
  eqR   : Eq Int

postulate
  _<ᴿ_  : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐓 ⟫
  _+ᴿ_  : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐑 ⟫
  _∧ᵀ_  : ⟪ 𝐓 →ᶜ 𝐓 →ᶜ 𝐓 ⟫

postulate instance
  eqIde : Eq Ide

postulate unknown : Loc

postulate initial-env : ⟪ 𝐔 ⟫
--"/hide"

assign : ⟪ 𝐋 →ᶜ 𝐄 →ᶜ 𝐂 →ᶜ 𝐂 ⟫      -- assign α ϵ stores ϵ at location α
assign α ϵ θ σ = θ (σ [ ϵ / α ]⊥)

hold : ⟪ 𝐋 →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂 ⟫      -- hold α gives the value stored at α
hold α κ σ = κ (σ α) σ
```
In the continuation-passing style used to define auxilary functions for Scm,
giving explicit continuity proofs would be particulary tedious.
For example, the function `hold` is simply a combination of
$\lambda$-abstraction and application, which is wellknown to ensure continuity.
```agda
postulate new : ⟪ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫  -- new gives an unallocated location

alloc : ⟪ 𝐄 →ᶜ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫     -- alloc ϵ allocates a location for ϵ
alloc ϵ κ = new (λ α → assign α ϵ (κ α))
--"hide"

postulate initial-store : ⟪ 𝐒 ⟫    -- may have initialised locations

postulate finished : ⟪ 𝐒 →ᶜ 𝐀 ⟫    -- obtain answer from the final store
--"/hide"

truish : ⟪ 𝐄 →ᶜ 𝐓 ⟫  -- truish ε is true for all ε except false
truish ϵ =  (ϵ ∈⊥ 𝐓) ⟶ (((ϵ |⊥ 𝐓) ==⊥ ↑ false) ⟶ ↑ false , ↑ true) ,
            ↑ true
```
The remaining auxiliary function definitions shown here involve the operations for (finite) sequences `ϵ⋆`
[Notation.Products.Sequences] [(MFPS2026-Agda)].
```agda
cons : ⟪ 𝐅 ⟫         -- cons ⟨ ϵ₁ , ϵ₂ ⟩ allocates and initialises a pair
cons ϵ⋆ κ =  (# ϵ⋆ ==⊥ ↑ 2) ⟶
                alloc (ϵ⋆ ↓ 1) (λ α₁ →
                  alloc (ϵ⋆ ↓ 2) (λ α₂ → κ ((α₁ , α₂) in⊥ 𝐄))) ,
              ⊥
```
In [(Mosses2025CSE)] the auxiliary function $\textit{list}$ is defined by recursion on `ϵ⋆`.
Agda accepts recursive definitions only when it can mechanically prove that the recursion terminates,
which is not the case for arguments in postulated types.
The following definition uses the postulated operation `fix` to avoid recursion.
```agda
list : ⟪ 𝐅 ⟫         -- list ϵ⋆ allocates and initialises a list
list =  fix λ (list′ : ⟪ 𝐅 ⟫) → λ ϵ⋆ κ →
          (# ϵ⋆ ==⊥ ↑ 0) ⟶ κ (↑ null in⊥ 𝐄) ,
          list′ (ϵ⋆ † 1) (λ ϵ → cons ⟨ (ϵ⋆ ↓ 1) , ϵ ⟩ κ)
--"hide"

car : ⟪ 𝐅 ⟫          -- car ⟨ ϵ ⟩ gives the head of the list ϵ
car ϵ⋆ κ = (# ϵ⋆ ==⊥ ↑ 1) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₁) κ , ⊥

cdr : ⟪ 𝐅 ⟫          -- cdr ⟨ ϵ ⟩ gives the tail of the list ϵ
cdr ϵ⋆ κ = (# ϵ⋆ ==⊥ ↑ 1) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₂) κ , ⊥

setcar : ⟪ 𝐅 ⟫       -- setcar ⟨ ϵ₁ , ϵ₂ ⟩ stores ϵ₂ in the head of list ϵ₁
setcar ϵ⋆ κ =
  (# ϵ⋆ ==⊥ ↑ 2) ⟶
    assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₁) (ϵ⋆ ↓ 2) (κ (↑ unspecified in⊥ 𝐄)) ,
  ⊥

setcdr : ⟪ 𝐅 ⟫       -- setcdr ⟨ ϵ₁ , ϵ₂ ⟩ stores ϵ₂ in the tail of list ϵ₁
setcdr ϵ⋆ κ =
  (# ϵ⋆ ==⊥ ↑ 2) ⟶
    assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₂) (ϵ⋆ ↓ 2) (κ (↑ unspecified in⊥ 𝐄)) ,
  ⊥
--"/hide"
```

[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/
[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[Notation.Products.Sequences]: ../../Notation.md#sequences