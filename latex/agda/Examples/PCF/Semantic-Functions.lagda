\subsubsection{Semantic functions}\label{Examples/PCF-Semantic-Functions-semantic-functions}

The notation \AgdaRef{ρ\ ⟦\ α\ i\ σ\ ⟧} gives the value of the variable
\AgdaRef{α\ i\ σ} in \AgdaRef{ρ} by applying \AgdaRef{ρ\ σ} to the
variable.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

\end{code}
\begin{code}
module Examples.PCF.Semantic-Functions where
\end{code}
\begin{code}[hide]

open import Notation
open import Examples.PCF.Abstract-Syntax
open import Examples.PCF.Domain-Equations

\end{code}
\begin{code}
_⟦_⟧ : Env → Vars σ → ⟪ 𝒟 σ ⟫     -- typed variable denotations
ρ ⟦ α i σ ⟧ = ρ σ (α i σ)
\end{code}
\end{AgdaSuppressSpace}
%
The semantic function \AgdaRef{𝒜⟦\ c\ ⟧} gives the standard
interpretation of the constant \AgdaRef{c}. The corresponding definitions
in \cite{Plotkin1977LCP}
use case analysis on the domain \AgdaRef{𝒟\ ι}, which is not supported in
our Agda formalisation (partly because it can express non-continuous
functions).
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]

open Notation.Flat using (↑; _♯)
open Notation.Flat.Booleans using (_⟶_,_; _==⊥_; false; true)
open Notation.Flat.Naturals using (_+_; _-_)

\end{code}
\begin{code}
𝒜⟦_⟧ : ℒᴬ σ → ⟪ 𝒟 σ ⟫             -- typed constant denotations
𝒜⟦ tt ⟧    =  ↑ true
𝒜⟦ ff ⟧    =  ↑ false
𝒜⟦ ⊃ ⟧     =  λ β δ₁ δ₂ → (β ⟶ δ₁ , δ₂)
𝒜⟦ Y ⟧     =  fix
𝒜⟦ k n ⟧   =  ↑ n
𝒜⟦ ⦅+1⦆ ⟧  =  (λ n → ↑ (n + 1)) ♯
𝒜⟦ ⦅−1⦆ ⟧  =  (λ n → ↑ (n ==ᴺ 0) ⟶ ⊥ , ↑ (n - 1)) ♯
𝒜⟦ Z ⟧     =  (λ n → ↑ (n ==ᴺ 0)) ♯
\end{code}
\end{AgdaSuppressSpace}
%
The semantic function \AgdaRef{𝒜′⟦\ M\ ⟧} is written
\(\hat{\mathcal A} \llbracket M \rrbracket\) in
\cite{Plotkin1977LCP}.
It gives the denotation of the term \AgdaRef{M} as a function of the
environment \AgdaRef{ρ}.
%
\begin{AgdaSuppressSpace}
\begin{code}
𝒜′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫  -- typed term denotations
𝒜′⟦ 𝑉 α i σ ⟧ ρ           =  ρ ⟦ α i σ ⟧
𝒜′⟦ 𝐿 c ⟧ ρ               =  𝒜⟦ c ⟧
𝒜′⟦ ⦅ M ␣ N ⦆ ⟧ ρ         =  𝒜′⟦ M ⟧ ρ (𝒜′⟦ N ⟧ ρ) 
𝒜′⟦ ⦅λ α i σ ␣ M ⦆ ⟧ ρ x  =  𝒜′⟦ M ⟧ (ρ [ x / α i σ ]′)
\end{code}
\end{AgdaSuppressSpace}
%
Comparison with Plotkin's original definition of PCF
\cite{Plotkin1977LCP}
confirms the directness of our Agda formalisation.
