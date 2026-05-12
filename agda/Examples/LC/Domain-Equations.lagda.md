# Domain Equations

The postulate below declares `unfold : ⟪ D∞ →ᶜ (D∞ →ᶜ D∞) ⟫` and
`fold : ⟪ (D∞ →ᶜ D∞) →ᶜ D∞~⟫`, corresponding to a
bijection between the domain `D∞` and the domain of
continuous endofunctions on `D∞`. (Simply defining
`D∞ = (D∞ →ᶜ D∞)` would lead to non-termination of the Agda
type-checker.)
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Examples.LC.Domain-Equations where
--"hide"

open import Examples.LC.Abstract-Syntax
open import Notation
open Recursion using (_≅_; fold; unfold) public

--"/hide"
postulate
  D∞ : Domain                      -- corresponds to Scott's domain 
  instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)  -- bijection
--"hide"
variable δ : ⟪ D∞ ⟫

--"/hide"
Env = Var →ˢ D∞  -- environments
--"hide"
variable ρ : ⟪ Env ⟫
--"/hide"
```
Use of the conventional notation
`ρ [ δ / v ]` for updating an environment `ρ`
to map `v` to `d` requires
an equality test for variables [(MFPS2026-Agda)].
```agda
--"hide"
open Notation.Flat.Booleans using (Bool; Eq; _==_)
open Notation.Flat.Naturals using (eqNat)
_==ⱽ_ : Var → Var → Bool
open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
open Notation.Updates using (_[_/_]) public
(x n ==ⱽ x n′) = (n ==ᴺ n′)
instance eqVar : Eq Var; _==_ {{eqVar}} = _==ⱽ_
--"/hide"
```

[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/