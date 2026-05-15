\section{Background}\label{Background-background}

\href{https://pdmosses.github.io/mfps2026-agda/Background/\#denotational-semantics}{Denotational Semantics} (Section~\ref{Background-denotational-semantics})
recalls the main concepts and notation of Scott--Strachey denotational
semantics. \href{https://pdmosses.github.io/mfps2026-agda/Background/\#agda}{Agda} (Section~\ref{Background-agda}) highlights features of the
Agda language whose use or meaning might not be immediately obvious.

\subsection{Denotational Semantics}\label{Background-denotational-semantics}

A conventional Scott--Strachey denotational semantics of a programming
language consists of definitions of \emph{abstract syntax},
\emph{semantic domains}, and \emph{semantic functions}. The abstract
syntax uses a context-free grammar to define sets of abstract syntax
trees (ASTs) that model the compositional structure of programs and
their phrases. The semantic domains are defined by equations in terms of
domain constructors, and can be mutually recursive. The semantic
functions are defined inductively, also with mutual recursion, and map
ASTs to their denotations, which are elements of domains. The denotation
of an AST models its contribution to the semantics of complete programs,
and is defined compositionally in terms of the denotations of its direct
components. The arguments of semantic functions are enclosed by
\(\llbracket\dots\rrbracket\), to avoid potential confusion between
abstract syntax terms and semantic notation.

Domains were originally continuous lattices
\cite{Scott1970OMT,Scott1972CL,Stoy1977DSS,Tennent1976DSP}.
A more general notion of domain is a dcpo (an algebraic,
bounded-complete and directed-complete partial order)
\cite{Abramsky1995DT}.
The notation for domain constructors and their accompanying operations
in a conventional Scott--Strachey semantics, summarised below, is
independent of the mathematical structure of domains. Let \(D, E\) be
domains, \(\delta : D\), and \(\epsilon : E\).

\begin{itemize}
\item
  Every domain \(D\) has a `bottom' element \(\bot_D\) that represents
  absence of information (e.g., due to an error or nontermination of a
  computation), usually written just \(\bot\).
\item
  A function \(\phi : D \to E\) is (Scott-) continuous if it is monotone
  and preserves limits of directed subsets of \(D\)
  \cite{Abramsky1995DT}.
  A function domain \(F = D \to E\) consists of continuous (total)
  functions from \(D\) to \(E\). The set of all functions from a set
  \(A\) to a domain also forms a domain, ordered point-wise. Functions
  between domains are defined using abstraction
  \(\lambda \delta.\epsilon\), application \(\phi\,\delta\), the
  operation \(\AgdaRef{fix}\) that maps each \(\phi : D \to D\) to its
  least fixed point, and the operations associated with other domain
  constructors.
\item
  For any set \(A\) the flat domain \(A_\bot\) is formed by adding
  \(\bot\) to \(A\). Functions on sets are implicitly extended to
  (continuous) functions on flat domains, returning \(\bot\) when any
  argument is \(\bot\). Elements \(\tau\) of the domain of truth-values
  \(\textbf{T} = \{ \text{true}, \text{false} \}_\bot\) are used in
  conditionals written \(\tau \to \delta_1, \delta_2\), where
  \(\text{true} \to \delta_1, \delta_2\) is \(\delta_1\),
  \(\text{false} \to \delta_1, \delta_2\) is \(\delta_2\), and
  \(\bot_{\textbf{T}} \to \delta_1, \delta_2\) is \(\bot_D\).
\item
  A separated sum domain \(X = \ldots + Y + \ldots\) consists of
  injected elements written `\(\upsilon \textsf{ in } X\)' (where
  \(\upsilon : Y\) for some summand \(Y\)) together with \(\bot_X\). The
  \(\textbf{T}\)-valued operation \(\chi \mathbin{\textsf{E}} Y\) tests
  whether \(\chi : X\) is the injection of some \(\upsilon : Y\); if so,
  \(\chi \mid Y\) projects \(\chi\) to \(\upsilon\), otherwise to
  \(\bot_Y\).
\item
  A cartesian product domain \(P = D \times E\) consists of pairs
  \(\langle \delta, \epsilon \rangle\) with
  \(\bot_P = \langle \bot_D, \bot_E \rangle\). When \(\pi : P\), the
  operations \(\pi \downarrow 1\) and \(\pi \downarrow 2\) select its
  components; similarly for domains of \(n\)-tuples \(D^n\) and finite
  sequences~\(D^*\). Further operations on \(D^*\) include the empty
  sequence \(\langle \rangle\), concatenation
  \(\delta^*_1 \mathbin{\S} \delta^*_2\), length
  \(\text{\#}\,\delta^*\), \(n\)th component \(\delta^* \downarrow n\),
  and \(n\)th tail \(\delta^* \mathbin{\dagger} n\) (\(n \geq 1\)).
\end{itemize}

Bob Tennent's highly accessible tutorial on denotational semantics
\cite{Tennent1976DSP} includes
illustrative examples (partly in continuation-passing style) and further
details of the conventional Scott--Strachey style.

\subsection{Agda}\label{Background-agda}

Agda
\cite{Agda-Language,Agda-Wikipedia}
is both a strongly typed functional programming language with support
for first-class \emph{dependent types} and a \emph{proof assistant}
based on the Curry-Howard correspondence between propositions and types.
A number of features set Agda apart from a typical functional
programming language:

\begin{itemize}
\item
  Types in Agda are first-class values of a \emph{universe}
  \(\textsf{Set}_i\) where \(\textsf{Set} = \textsf{Set}_0\), and each
  universe \(\textsf{Set}_i\) belongs to the next universe
  \(\textsf{Set}_{i+1}\).
\item
  Agda has \emph{dependent function types} \AgdaRef{(x\ :\ A)\ →\ B} or
  \AgdaRef{∀\ x\ →\ B} where the type \AgdaRef{B} can depend on the value
  \AgdaRef{x}.
\item
  All functions in Agda are \emph{total}: evaluating a function call is
  guaranteed to return a value of the correct type in finite time. To
  ensure totality, Agda's type checker includes a termination check for
  recursive definitions, a positivity check for inductive datatypes, and
  a consistency check for universe levels.
\end{itemize}

Thanks to its dependent types and totality, Agda's type system can be
used as a higher-order logic for writing mathematical statements and
proofs, where types correspond to propositions and type checking
corresponds to checking the validity of the proof.

\subsubsection*{Some notes on Agda's syntax and
features}\label{Background-some-notes-on-agdas-syntax-and-features}
\addcontentsline{toc}{subsubsection}{Some notes on Agda's syntax and
features}

\begin{description}
\tightlist
\item[Naming.]
Defined symbols, variables, and type constructors all share a single
namespace. Names can be any sequence of ASCII and Unicode characters
except \AgdaRef{.;\{\}()@"}.
\item[Anonymous functions.]
Lambda expressions use the syntax \AgdaRef{λ\ x\ →\ u} instead of
\AgdaRef{λ\ x.\ u}.
\item[Mixfix notation.]
Agda supports \emph{mixfix notation} for defining operators, with
underscores in the name of a symbol indicating argument positions. For
example, if we declare \AgdaRef{\_+\_\ :\ Nat\ →\ Nat\ →\ Nat}, we can
use it as \AgdaRef{1\ +\ 1} (the spaces are required, since \AgdaRef{1+1}
is a valid Agda name!).
\item[Implicit arguments.]
Arguments marked by single curly braces \AgdaRef{\{...\}} in the type of
a symbol are considered to be \emph{implicit}. These arguments may be
omitted, and are then inferred by Agda's type checker.
\item[Type classes.]
Agda has no direct support for type classes, but they can be simulated
using Agda's \emph{instance arguments} to resolve type class instances.
Instance arguments are marked by double curly braces
\AgdaRef{\{\{...\}\}} and are resolved automatically by using definitions
marked as \AgdaRef{instance}.
\item[Rewrite rules.]
Agda has support for \emph{rewrite rules}
\cite{cockx:LIPIcs.TYPES.2019.2,Cockx2021TRT}
that are applied automatically during type checking. Rewrite rules are
declared by marking proofs of the equality type \AgdaRef{a\ ≡\ b} with a
\AgdaRef{REWRITE} pragma.
\end{description}
