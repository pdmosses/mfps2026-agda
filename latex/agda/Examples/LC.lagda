\subsection{Untyped Lambda-Calculus}\label{Examples/LC-untyped-lambda-calculus}

This section presents an Agda formalisation of a denotational semantics
of the untyped \(\lambda\)-calculus.  Elided module imports are
included in the
\href{https://pdmosses.github.io/mfps2026-agda/Examples/LC/Domain-Equations/}{complete
code listing}. 
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
