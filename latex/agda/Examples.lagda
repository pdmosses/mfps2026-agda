\section{Illustrative Examples}\label{Examples-illustrative-examples}

This section illustrates mechanisation of denotational semantics in Agda
with three examples, all using the
postulated notation (Section~\ref{Notation-postulated-domain-notation}\,\href{https://pdmosses.github.io/mfps2026-agda/Notation/\#postulated-domain-notation}{$\Uparrow$})
for domains and their associated operations: the
Untyped
Lambda-Calculus (Section~\ref{Examples/LC-untyped-lambda-calculus}\,\href{https://pdmosses.github.io/mfps2026-agda/Examples/LC/\#untyped-lambda-calculus}{$\Uparrow$}),
PCF:
A Programming Language for Computable Functions (Section~\ref{Examples/PCF-pcf-a-programming-language-for-computable-functions}\,\href{https://pdmosses.github.io/mfps2026-agda/Examples/PCF/\#pcf-a-programming-language-for-computable-functions}{$\Uparrow$}), and
Scm: A
Sublanguage of Scheme (Section~\ref{Examples/Scm-scm-a-sublanguage-of-scheme}\,\href{https://pdmosses.github.io/mfps2026-agda/Examples/Scm/\#scm-a-sublanguage-of-scheme}{$\Uparrow$}).
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
