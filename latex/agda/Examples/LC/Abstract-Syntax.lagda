\subsubsection{Abstract Syntax}\label{Examples/LC-Abstract-Syntax-abstract-syntax}

Abstract syntax is \emph{not} regarded as a domain. In conventional
Scott--Strachey style denotational semantics, abstract syntax is
generally first-order: terms are finite, totally-defined elements.

A variable is written \AgdaRef{x\ n}. The argument \AgdaRef{n} merely
distinguishes between variables -- it is \emph{not} a De Bruin index.
The term constructor \AgdaRef{var} below merely includes variables in
terms.

In Agda, mixfix notation requires argument positions to be separated by
characters other than spaces. Below, the constructors for function
abstraction and application use the Unicode character \AgdaRef{␣} as a
separator.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check #-}

\end{code}
\begin{code}
module Examples.LC.Abstract-Syntax where
\end{code}
\begin{code}[hide]

open import Agda.Builtin.Nat public using (Nat)

\end{code}
\begin{code}
data Var : Set where
  x : Nat → Var
\end{code}
\begin{code}[hide]
variable v : Var

\end{code}
\begin{code}
data Exp : Set where
  var_    : Var → Exp        -- variable reference
  ⦅λ_␣_⦆  : Var → Exp → Exp  -- function abstraction
  ⦅_␣_⦆   : Exp → Exp → Exp  -- function application
\end{code}
\begin{code}[hide]
variable e e₁ e₂ : Exp
\end{code}
\end{AgdaSuppressSpace}
