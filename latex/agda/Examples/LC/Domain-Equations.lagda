\subsubsection{Domain Equations}\label{Examples/LC/Domain-Equations-domain-equations}

Simply defining \AgdaRef{D∞\ =\ (D∞\ →ᶜ\ D∞)} would lead to
non-termination of the Agda type-checker. Instead, we postulate the
domain \AgdaRef{D∞}, together with a bijection
\AgdaRef{D∞\ ≅\ (D∞\ →ᶜ\ D∞)}. This declares
\AgdaRef{unfold\ :\ ⟪\ D∞\ →ᶜ\ (D∞\ →ᶜ\ D∞)\ ⟫} and
\AgdaRef{fold\ :\ ⟪\ (D∞\ →ᶜ\ D∞)\ →ᶜ\ D∞\ ⟫}.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

\end{code}
\begin{code}
module Examples.LC.Domain-Equations where
\end{code}
\begin{code}[hide]

open import Examples.LC.Abstract-Syntax
open import Notation
open Recursion using (_≅_; fold; unfold) public

\end{code}
\begin{code}
postulate
  D∞ : Domain                      -- corresponds to Scott's domain 
  instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)  -- bijection
\end{code}
\begin{code}[hide]
variable δ : ⟪ D∞ ⟫

\end{code}
\begin{code}
Env = Var →ˢ D∞  -- environments
\end{code}
\begin{code}[hide]
variable ρ : ⟪ Env ⟫
\end{code}
\end{AgdaSuppressSpace}
%
Use of the conventional notation \AgdaRef{ρ\ {[}\ δ\ /\ v\ {]}} for
updating an environment \AgdaRef{ρ} to map \AgdaRef{v} to \AgdaRef{d}
requires an equality test for variables, elided here.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
open Notation.Flat.Booleans using (Bool; Eq; _==_)
open Notation.Flat.Naturals using (eqNat)
_==ⱽ_ : Var → Var → Bool
open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
open Notation.Updates using (_[_/_]) public
(x n ==ⱽ x n′) = (n ==ᴺ n′)
instance eqVar : Eq Var
_==_ {{eqVar}} = _==ⱽ_
\end{code}
\end{AgdaSuppressSpace}
