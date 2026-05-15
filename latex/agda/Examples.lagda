\section{Illustrative Examples}\label{Examples-illustrative-examples}

This section illustrates mechanisation of denotational semantics in Agda
with three examples, all using the
\href{https://pdmosses.github.io/mfps2026-agda/Notation/\#postulated-domain-notation}{postulated notation} (Section~\ref{Notation-postulated-domain-notation})
for domains and their associated operations: the
\href{https://pdmosses.github.io/mfps2026-agda/Examples/LC/\#untyped-lambda-calculus}{Untyped
Lambda-Calculus} (Section~\ref{Examples/LC-untyped-lambda-calculus}),
\href{https://pdmosses.github.io/mfps2026-agda/Examples/PCF/\#pcf-a-programming-language-for-computable-functions}{PCF:
A Programming Language for Computable Functions} (Section~\ref{Examples/PCF-pcf-a-programming-language-for-computable-functions}), and
\href{https://pdmosses.github.io/mfps2026-agda/Examples/Scm/\#scm-a-sublanguage-of-scheme}{Scm: A
Sublanguage of Scheme} (Section~\ref{Examples/Scm-scm-a-sublanguage-of-scheme}).
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples where

import Examples.LC
import Examples.PCF
import Examples.Scm
\end{code}
\end{AgdaSuppressSpace}
