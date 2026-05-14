# Domain Equations

The domains for Scm are somewhat simpler than for the denotational semantics in
the Scheme standards [(Scheme)],
but still involve all our postulated domain constructors.
Using definitional equations instead of postulated domain equivalences `D ≅ E`
avoids the need for the functions `fold` and `unfold`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Examples.Scm.Domain-Equations where
--"hide"

open import Examples.Scm.Abstract-Syntax using (Ide; Int)
import Notation
open Notation.Domains using (Domain; ⟪_⟫)
open Notation.Functions using (_→ᶜ_; _→ˢ_)
open Notation.Flat using (_+⊥)
open Notation.Flat.Booleans using (Bool⊥)
open Notation.Flat.Naturals using (Nat⊥)
open Notation.Sums using (_≳_↦_)
open Notation.Products using (_×_)
open Notation.Products.Sequences using (_⋆)
--"/hide"

postulate Loc : Set
𝐋  =  Loc +⊥                -- locations
𝐍  =  Nat⊥                  -- natural numbers
𝐓  =  Bool⊥                 -- booleans
𝐑  =  Int +⊥                -- numbers
𝐏  =  𝐋 × 𝐋                 -- pairs
𝐔  =  Ide →ˢ 𝐋              -- environments
data Misc : Set where null unallocated undefined unspecified : Misc
𝐌  =  Misc +⊥               -- miscellaneous
```
The conventional denotational semantics of Scm [(Mosses2025CSE)] defines the domain $𝐄$
of expression values by the equation $𝐄 = 𝐓 + 𝐑 + 𝐏 + 𝐌 + 𝐅$,
and the domain $𝐅$ of procedure values by $𝐅 = 𝐄^* \to (𝐄 \to 𝐂) \to 𝐂$.
Mutually recursive groups of domain equations have well-defined solutions,
but in Agda, defining both the corresponding domains `𝐄` and `𝐅` by equations
would cause the type checker to diverge.
Postulating one (or both) of these domains avoids divergence;
postulating `𝐄` also has the benefit that the embeddings and projections for its summands
subsume the bijection between `𝐄` and its intended structure.
```agda
postulate 𝐄 : Domain        -- expressed values
𝐒  =  𝐋 →ᶜ 𝐄                -- stores
postulate 𝐀 : Domain        -- answers
𝐂  =  𝐒 →ᶜ 𝐀                -- command continuations
𝐅  =  𝐄 ⋆ →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂  -- procedure values
```
The following postulates instantiate embedding (`δ in⊥ 𝐄`),
inspection (`ε ∈⊥ D`),
and projection (`ε |⊥ D`) for each summand `D` of `𝐄`.
```agda
postulate instance
  E+=T  : 𝐄 ≳ 1 ↦ 𝐓
  E+=R  : 𝐄 ≳ 2 ↦ 𝐑
  E+=P  : 𝐄 ≳ 3 ↦ 𝐏
  E+=M  : 𝐄 ≳ 4 ↦ 𝐌
  E+=F  : 𝐄 ≳ 5 ↦ 𝐅
--"hide"

variable
  α : ⟪ 𝐋 ⟫;  ρ : ⟪ 𝐔 ⟫;  μ  : ⟪ 𝐌 ⟫;    ϵ : ⟪ 𝐄 ⟫
  σ : ⟪ 𝐒 ⟫;  θ : ⟪ 𝐂 ⟫;  ϵ⋆ : ⟪ 𝐄 ⋆ ⟫;   φ : ⟪ 𝐅 ⟫
--"/hide"
```

[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[(Scheme)]: https://standards.scheme.org