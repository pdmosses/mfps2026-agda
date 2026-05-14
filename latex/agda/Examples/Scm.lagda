\subsection{Scm: A Sublanguage of
Scheme}\label{Examples/Scm-scm-a-sublanguage-of-scheme}

Scm is a particularly basic sublanguage of the core Scheme expression
language whose denotational semantics is defined in the Scheme reports
\cite{Scheme}. The domains and auxiliary
functions declared in this section are explained in the presentation of
the conventional denotational semantics of Scm
\cite{Mosses2025CSE}; they
involve the notation for sequences summarised in §2.1 of the present
paper.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.Scm where

import Examples.Scm.Abstract-Syntax
import Examples.Scm.Domain-Equations
import Examples.Scm.Semantic-Functions
import Examples.Scm.Auxiliary-Functions
\end{code}
\end{AgdaSuppressSpace}
