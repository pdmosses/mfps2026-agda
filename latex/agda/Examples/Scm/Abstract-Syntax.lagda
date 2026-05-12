\subsubsection{Abstract Syntax}\label{Examples/Scm-Abstract-Syntax-abstract-syntax}

The following grammar
\cite{Mosses2025CSE}
summarises the abstract syntax of Scm expressions
\(\text{E} : \text{Exp}\) with integers \(\text{Z} : \text{Int}\),
constants \(\text{K} : \text{Con}\) and identifiers
\(\text{I} : \text{Ide}\). The meta-variable
\(\text{E}^* : \text{Exp}^*\) implicitly ranges over arbitrary sequences
of expressions. \begin{align}
  \text{K} & ::=
    \text{Z} \mid \AgdaRef{\#t} \mid \AgdaRef{\#f}
  \\
  \text{E} & ::=
    \text{K} \mid \text{I} \mid \texttt ( \text{E}_0~\text{E}^* \texttt ) \mid \AgdaRef{(lambda} ~ \text{I} ~ \text{E} \texttt ) \mid
    \AgdaRef{(if} ~ \text{E}_0 ~ \text{E}_1 ~ \text{E}_2 \texttt ) \mid \AgdaRef{(set!} ~ \text{I} ~ \text{E} \texttt )
\end{align} In the following Agda formalisation of the above grammar,
the abstract syntax of sequences \AgdaRef{E⋆\ :\ Exp⋆} is made explicit:
the empty sequence is represented by \AgdaRef{␣␣␣}, and sequence
prefixing by \AgdaRef{E\ ␣␣\ E⋆}.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check #-}

\end{code}
\begin{code}
module Examples.Scm.Abstract-Syntax where
\end{code}
\begin{code}[hide]

open import Data.String.Base public using (String)

\end{code}
\begin{code}
Ide = String      -- identifiers
\end{code}
\begin{code}[hide]
variable I : Ide

open import Data.Integer.Base public renaming (ℤ to Int) using ()
\end{code}
\begin{code}
data Con  : Set where  -- constants
  int     : Int → Con  -- integer numerals
  #t      : Con        -- true
  #f      : Con        -- false
\end{code}
\begin{code}[hide]
variable K : Con

\end{code}
\begin{code}
mutual
  data Exp       : Set where              -- expressions
    con          : Con → Exp              -- constants
    ide          : Ide → Exp              -- identifiers
    ⦅_␣_⦆        : Exp → Exp⋆ → Exp       -- procedure application 
    ⦅lambda_␣_⦆  : Ide → Exp → Exp        -- procedure abstraction
    ⦅if_␣_␣_⦆    : Exp → Exp → Exp → Exp  -- conditional choice
    ⦅set!_␣_⦆    : Ide → Exp → Exp        -- assignment
  data Exp⋆      : Set where              -- expression sequences
    ␣␣␣          : Exp⋆                   -- empty sequence
    _␣␣_         : Exp → Exp⋆ → Exp⋆      -- sequence prefix
\end{code}
\begin{code}[hide]
variable E : Exp; E⋆ : Exp⋆

mutual
  data Body      : Set where             -- bodies
    ␣␣_          : Exp → Body            -- expression body
    ⦅define_␣_⦆  : Ide → Exp → Body      -- definition body
    ⦅begin_⦆     : Body⁺ → Body          -- body sequence
  data Body⁺     : Set where             -- body sequences
    ␣␣_          : Body → Body⁺          -- empty sequence
    _␣␣_         : Body → Body⁺ → Body⁺  -- sequence prefix
data Prog        : Set where             -- programs
  ␣␣␣            : Prog                  -- empty program
  ␣␣_            : Body⁺ → Prog          -- body sequence program
variable B : Body; B⁺ : Body⁺; Π : Prog
\end{code}
\end{AgdaSuppressSpace}
