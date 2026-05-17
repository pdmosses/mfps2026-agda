\subsection{Untyped Lambda-Calculus}\label{Examples/LC-untyped-lambda-calculus}

This section presents our Agda embedding of a denotational semantics of
the untyped \(\lambda\)-calculus.
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
