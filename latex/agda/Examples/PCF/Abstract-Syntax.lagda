\subsubsection{Abstract Syntax}\label{Examples/PCF/Abstract-Syntax-abstract-syntax}

The following abstract syntax of well-formed PCF terms in Agda uses
indexed datatype definitions. PCF function types \(\sigma \to \tau\) are
written \AgdaRef{σ\ ⇒\ τ}, and variables \(\alpha_i^\sigma\) are written
\AgdaRef{α\ i\ σ} (where the argument \AgdaRef{i} merely distinguishes
between variables -- it is \emph{not} a De Bruijn index).
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

\end{code}
\begin{code}
module Examples.PCF.Abstract-Syntax where

\end{code}
\begin{code}[hide]
open import Notation

\end{code}
\begin{code}
data Types  : Set where                          -- type terms
  ι         : Types                              -- individuals
  o         : Types                              -- truth-values
  _⇒_       : Types → Types → Types              -- functions
\end{code}
\begin{code}[hide]
infixr 1 _⇒_
variable σ τ : Types

open import Agda.Builtin.Nat public using (Nat)
\end{code}
\begin{code}

data Vars   : Types → Set where                  -- typed variables
  α         : Nat → (σ : Types) → Vars σ         -- α i σ is a variable of type σ
\end{code}
\begin{code}[hide]
variable i  : Nat
\end{code}
\begin{code}

data ℒᴬ     : Types → Set where                  -- typed constants
  tt        : ℒᴬ o                               -- true
  ff        : ℒᴬ o                               -- false
  ⊃         : ℒᴬ (o ⇒ σ ⇒ σ ⇒ σ)                 -- conditional
  Y         : ℒᴬ ((σ ⇒ σ) ⇒ σ)                   -- fixed point
  k         : Nat → ℒᴬ ι                         -- numerals
  ⦅+1⦆      : ℒᴬ (ι ⇒ ι)                         -- successor
  ⦅−1⦆      : ℒᴬ (ι ⇒ ι)                         -- predecessor
  Z         : ℒᴬ (ι ⇒ o)                         -- zero test
\end{code}
\begin{code}[hide]
variable c  : ℒᴬ σ
\end{code}
\begin{code}

data Terms  : Types → Set where                  -- typed terms
  𝑉_        : Vars σ → Terms σ                   -- variable
  𝐿_        : ℒᴬ σ → Terms σ                     -- constant
  ⦅_␣_⦆     : Terms (σ ⇒ τ) → Terms σ → Terms τ  -- function application
  ⦅λ_␣_⦆    : Vars σ → Terms τ → Terms (σ ⇒ τ)   -- function abstraction
\end{code}
\begin{code}[hide]
variable M N : Terms σ
\end{code}
\end{AgdaSuppressSpace}
