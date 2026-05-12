\subsection{PCF}\label{Examples-PCF-pcf}

PCF and its denotational semantics were orginally defined by Dana Scott
in 1969
\cite{Scott1993TTA} with
combinators (\AgdaRef{S}, \AgdaRef{K}) instead of \(\lambda\)-abstraction.
Gordon Plotkin subsequently defined a denotational semantics for PCF
including \(\lambda\)-abstraction
\cite{Plotkin1977LCP}.
The Agda modules presented below formalise the latter definition.

PCF is an intrinsically typed language: every well-formed term has a
unique type. The following grammar summarises the context-free abstract
syntax of types \(\sigma, \tau\) and terms \(M, N\) with variables
\(\alpha_i^\sigma\) (\(i \geq 0\)) and constants \(c\). In §4.1.1 we
reflect Plotkin's presentation of PCF more accurately by exploiting
Agda's support for dependent types. \begin{align}
  \sigma, \tau  & ::=
    \iota \mid o \mid (\sigma \to \tau)
  \\
  c & ::=
    \textit{tt} \mid \textit{ff} \mid {\supset} \mid \textbf{Y} \mid
    k_n \mid (+1) \mid (-1) \mid \textbf{Z}
  \\
  M, N & ::=
    \alpha_i^\sigma \mid c \mid (M \, N) \mid (\lambda \alpha_i^\sigma M)
\end{align}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.PCF where

import Examples.PCF.Abstract-Syntax
import Examples.PCF.Domain-Equations
import Examples.PCF.Semantic-Functions
\end{code}
\end{AgdaSuppressSpace}
