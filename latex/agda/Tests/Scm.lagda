\subsection{Scm Tests}\label{Tests-Scm-scm-tests}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check #-}

\end{code}
\begin{code}
module Tests.Scm where
\end{code}
\begin{code}[hide]
open import Examples.Scm.Abstract-Syntax
open import Examples.Scm.Domain-Equations
open import Examples.Scm.Auxiliary-Functions
open import Examples.Scm.Semantic-Functions

open import Notation
open Notation.Flat
open Notation.Flat.Booleans
open Notation.Sums
open import Properties
open Properties.Flat
open Properties.Flat.Booleans
open Properties.Sums
\end{code}
\begin{code}

check-sum : {β : ⟪ 𝐓 ⟫} → (β in⊥ 𝐄) ∈⊥ 𝐓 ≡ ↑ true
check-sum = refl
\end{code}
\end{AgdaSuppressSpace}
