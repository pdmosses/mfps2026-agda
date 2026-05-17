\subsubsection{Domain Equations}\label{Examples/PCF/Domain-Equations-domain-equations}

The domains \AgdaRef{𝒟\ σ} form a ``standard collection of domains for
arithmetic'' in PCF, written \(\mathcal D_\sigma\) in
\cite{Plotkin1977LCP}.
As PCF is a simply-typed language, the domains \AgdaRef{𝒟\ σ} are not
reflexive, so their embedding in Agda can use ordinary type definitions,
not involving bijections.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

\end{code}
\begin{code}
module Examples.PCF.Domain-Equations where
\end{code}
\begin{code}[hide]

open import Examples.PCF.Abstract-Syntax
open import Notation
open Notation.Flat.Booleans using (Bool; Bool⊥)
open Notation.Flat.Naturals using (Nat⊥; eqNat)
\end{code}
\begin{code}

𝒟 : Types → Domain       -- standard domains
𝒟 ι        = Nat⊥        -- natural numbers
𝒟 o        = Bool⊥       -- truth-values
𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ  -- functions
\end{code}
\begin{code}[hide]
variable x y z : ⟪ 𝒟 σ ⟫
\end{code}
\end{AgdaSuppressSpace}
%
Environments \AgdaRef{ρ} are type-preserving maps from variables to
values. They are naturally modeled by a dependent type: \AgdaRef{Env\ σ}
consists of type-preserving maps from variables in \AgdaRef{Vars\ σ} to
their values in the domain \AgdaRef{𝒟\ σ}. The environment \AgdaRef{ρ⊥}
maps all variables to \AgdaRef{⊥}.
%
\begin{AgdaSuppressSpace}
\begin{code}
Env = (σ : Types) → ⟪ Vars σ →ˢ 𝒟 σ ⟫  -- typed environments
\end{code}
\begin{code}[hide]
variable ρ : Env
\end{code}
\begin{code}
ρ⊥ : Env                               -- initial environment
ρ⊥ _ _ = ⊥
\end{code}
\end{AgdaSuppressSpace}
%
Extension or overriding environments requires instances of the equality
tests for both variables and types. The definition of the latter is
somewhat tedious.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
open Notation.Flat.Booleans using (Eq; _==_)
open Notation.Updates using (_[_/_])
_==ⱽ_ : Vars σ → Vars σ → Bool
open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
(α i σ ==ⱽ α i′ σ)  =  (i ==ᴺ i′)
instance
  eqV : Eq (Vars σ)
  _==_ {{eqV}} = _==ⱽ_
open Notation.Updates using (MaybeEq; _==?_; just; nothing; refl; _[_←_])
instance
  eqT : MaybeEq Types
  eqT ._==?_ ι ι = just refl
  eqT ._==?_ o o = just refl
  eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁) with σ ==? σ₁  | τ ==? τ₁
  eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁)    | just refl | just refl = just refl
  eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁)    | _         | _         = nothing
  eqT ._==?_ _ _ = nothing

_[_/_]′ : Env → ⟪ 𝒟 σ ⟫ → Vars σ → Env
-- ρ [ v / x ]′ maps x to v, and other x′ to ρ x′
_[_/_]′ {σ} ρ x v = ρ [ σ ← ρ σ [ x / v ] ]
\end{code}
\end{AgdaSuppressSpace}
