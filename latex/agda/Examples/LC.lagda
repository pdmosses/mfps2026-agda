\subsection{Untyped λ-calculus}\label{Examples-LC-untyped-ux3bb-calculus}

This section presents an Agda formalisation of a denotational semantics
of the untyped \(\lambda\)-calculus. Elided module imports are shown in
the complete code
\cite{MFPS2026-Agda}.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.LC where

import Examples.LC.Abstract-Syntax
import Examples.LC.Domain-Equations
import Examples.LC.Semantic-Functions
\end{code}
\end{AgdaSuppressSpace}
%
See the \href{https://pdmosses.github.io/mfps2026-agda/Tests/LC/}{\AgdaRef{Tests}} module for some examples of
abstract syntax terms and equivalence proofs.
