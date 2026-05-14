\subsubsection{Semantic Functions}\label{Examples/LC/Semantic-Functions-semantic-functions}

The semantic equations below correspond closely to those found in
textbooks on denotational semantics (e.g.,
\cite{Reynolds1998TPL}).
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

\end{code}
\begin{code}
module Examples.LC.Semantic-Functions where
\end{code}
\begin{code}[hide]

open import Examples.LC.Abstract-Syntax
open import Examples.LC.Domain-Equations
open import Notation

\end{code}
\begin{code}
⟦_⟧ : Exp → ⟪ Env →ᶜ D∞ ⟫
⟦ var v ⟧ ρ        = ρ v
⟦ ⦅λ v ␣ e ⦆ ⟧ ρ   = fold ( λ δ → ⟦ e ⟧ (ρ [ δ / v ]) )
⟦ ⦅ e₁ ␣ e₂ ⦆ ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
\end{code}
\end{AgdaSuppressSpace}
