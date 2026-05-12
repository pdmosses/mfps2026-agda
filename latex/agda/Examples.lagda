\section{Illustrative Examples}\label{agda-Examples-illustrative-examples}

This section illustrates mechanisation of denotational semantics in Agda
with three examples, all using the posulated
\href{https://pdmosses.github.io/mfps2026-agda/Notation/}{\AgdaRef{Notation}} for domains and their associated
operations: Untyped Lambda-Calculus \href{https://pdmosses.github.io/mfps2026-agda/LC/index/}{\AgdaRef{LC}} (§4.1),
Programming Computable Functions \href{https://pdmosses.github.io/mfps2026-agda/PCF/index/}{\AgdaRef{PCF}} (§4.2), a
simple sublanguage \href{https://pdmosses.github.io/mfps2026-agda/Scm/index/}{\AgdaRef{Scm}} of Scheme
\cite{Scheme} (§4.3).
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

import Examples.LC
import Examples.PCF
import Examples.Scm
\end{code}
\end{AgdaSuppressSpace}
