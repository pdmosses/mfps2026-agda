# Background

This section briefly recalls the main features of Scott–Strachey denotational semantics,
and summarises the notation conventionally used in denotational descriptions of programming languages.
It then mentions significant features of the Agda language,
and explains some Agda syntax used in the subsequent sections.

## Denotational Semantics

### Features

A denotational semantic description of a programming language specifies
*abstract syntax*, *semantic domains*, and *semantic functions*.

Abstract syntax.
:   An abstract syntax defines semantically-relevant sets of phrases
    (e.g., commands, declarations, expressions) and their compositional structure.
    Phrases are regarded as *abstract syntax trees* (ASTs), rather than as strings of symbols.

    Abstract syntax is specified by a *context-free grammar*.
    The nonterminal symbols of the grammar correspond to named sets of ASTs.
    BNF-like productions determine notation for AST node constructors.

Semantic domains.
:   The *denotation* of a phrase models the contribution of that phrase
    to the semantics of all programs in which it occurs.
    Semantic domains are sets of abstract mathematical values (e.g., functions, tuples, truth values)
    used to construct denotations.

    Semantic domains are specified by *domain equations* that defined named semantic domains
    in terms of standard *domain constructors*.
    The definitions can be mutually recursive.

Semantic functions.
:   These functions map abstract phrases to their denotations.
    They are required to be *compositional*:
    the denotation of a phrase depends on the denotations of its sub-phrases,
    but it cannot depend on their syntax.

    Semantic functions are specified inductively by *semantic equations*.
    Their AST arguments are enclosed by $\llbracket\dots\rrbracket$,
    avoiding potential confusion between notation for AST constructors and elements of domains.

### Domain Notation

Domains were originally required to be *continuous lattices*
[(Scott1970OMT)]\ [(Scott1972CL)]\ [(Stoy1977DSS)]\ [(Tennent1976DSP)].
Various more general notions of domain have been suggested (e.g., see [(Abramsky1995DT)])
but here it is only important that endofunctions between domains have *fixed points*,
recursive *domain equations* have well-defined solutions (up to isomorphism),
and each domain comes with a *bottom element*.
The conventional notation for domain constructors and their accompanying operations,
summarised below, is independent of the exact notion of domains.

Domains
:   Every domain $D$ has a *bottom* element $\bot_D$ that represents
    absence of information (e.g., due to an error or nontermination of a
    computation), usually written just $\bot$.

Function domains.
:   A function $\phi : D \to E$ is (Scott-)*continuous* if it is monotone and
    preserves limits of directed subsets of\ $D$\ [(Abramsky1995DT)].
    The *function domain* $F = D \to E$ consists of all continuous (total) functions from $D$ to $E$.
    The set of all functions from a set\ $A$ to a domain also forms a domain, ordered pointwise.

    Functions between domains are always continuous when they are defined using
    abstraction $\lambda \delta.\epsilon$, application $\phi\,\delta$,
    the operation $\textit{fix}$ that maps each endofunction $\phi : D \to D$ to its least fixed point,
    and the operations associated with other domain constructors.

Flat domains.
:   For any set $A$ the *flat domain* $A_\bot$ is formed by adding $\bot$ as a fresh element.
    Functions on sets are implicitly extended to (continuous) functions on flat domains,
    returning\ $\bot$ when any argument is\ $\bot$.

    Elements\ $\tau$ of the domain of *truth-values* $\textbf{T} = \{ \textit{true}, \textit{false} \}_\bot$
    are used in *conditionals* written $\tau \to \delta_1, \delta_2$\ ,
    where $\textit{true} \to \delta_1, \delta_2$ is $\delta_1$\ ,
    $\textit{false} \to \delta_1, \delta_2$ is $\delta_2$\ , and
    $\bot_{\textbf{T}} \to \delta_1, \delta_2$ is $\bot_D$\ .

Sum domains.
:   The *separated sum domain* $X = \ldots + Y + \ldots$ consists of injected elements
    written '$\upsilon \textsf{ in } X$' (where $\upsilon : Y$ for some summand $Y$)
    together with $\bot_X$.

    The $\textbf{T}$-valued operation $\chi \mathbin{\textsf{E}} Y$
    (written $\chi \in Y$ in [(Scheme)])
    tests whether $\chi : X$ is the injection of some $\upsilon : Y$;
    if so, $\chi \mid Y$ projects $\chi$ to $\upsilon$, otherwise to $\bot_Y$.

Product domains.
:   The *product domain* $P = D \times E$ consists of pairs $\langle \delta, \epsilon \rangle$
    with $\bot_P = \langle \bot_D, \bot_E \rangle$.
    When $\pi : P$, the operations $\pi \downarrow 1$ and $\pi \downarrow 2$ select its components.

    The domain of $n$-*tuples* $\langle \delta_1, \ldots, \delta_n \rangle$ of elements of $D$
    is written\ $D^n$, and the domain of all finite *sequences* is written\ $D^*$.
    Further operations on\ $D^*$ include the empty sequence\ $\langle \rangle$,
    concatenation\ $\delta^*_1 \mathbin{\S} \delta^*_2$, length\ $\textit{\#}\,\delta^*$,
    $n$th\ component $\delta^* \downarrow n$, and $n$th\ tail $\delta^* \mathbin{\dagger} n$ ($n \geq 1$).

Recursive domains
:   In a collection of domain equations $D_i = E_i$, the $D_i$ are distinct domain names,
    and the $E_i$ are domain terms formed from domain constructors and domain names,
    allowing unrestricted recursion.
    However, the solution of the equations is up to an isomorphism
    (written $\phi : D_i \to E_i$\ , $\psi : E_i \to D_i$ in [(Reynolds1998TPL)],
    and $\textit{unfold} : D_i \to E_i$\ , $\textit{fold} : E_i \to D_i$ in [(Abramsky1995DT)],
    but usually left implicit).

Updates.
:   The *update* $\phi[\epsilon / \delta]$ of a function $\phi : D \to E$ maps $\delta$ to $\epsilon$,
    and all other elements $\delta'$ in $D$ to $\phi(\delta')$.
    The domain $D$ has to be flat (with a continuous equality);
    the same notation is used when $D$ is a set.


## Agda

### Features

Agda [(Agda-Language)]\ [(Agda-Wikipedia)] is both a strongly typed
functional *programming language* with support for first-class
*dependent types* and a *proof assistant* based on the Curry–Howard
correspondence between propositions and types. A number of features set
Agda apart from a typical functional programming language:

- Types in Agda are first-class values of a *universe* $\textsf{Set}_i$ where
  $\textsf{Set} = \textsf{Set}_0$, and each universe $\textsf{Set}_i$
  belongs to the next universe $\textsf{Set}_{i+1}$.

- Agda has *dependent function types* `(x : A) → B` or `∀ x → B`
  where the type `B` can depend on the value `x`.

- All functions in Agda are *total*: evaluating a function call is
  guaranteed to return a value of the correct type in finite time. To
  ensure totality, Agda's type checker includes a termination check for
  recursive definitions, a positivity check for inductive datatypes, and
  a consistency check for universe levels.

Thanks to its dependent types and totality, Agda's type system can be
used as a higher-order logic for writing mathematical statements and
proofs, where types correspond to propositions and type checking
corresponds to checking the validity of the proof.

### Agda Syntax

The following syntactic constructs are used in the subsequent sections,
and could be unclear to readers unfamiliar with Agda.

Comments.
:   End-of-line comments are initiated by `--`, while multi-line comments
    are between `{-` and `-}`.

Naming.
:   Declared symbols, variables, and type constructors all share a
    single namespace. Names can be any sequence of non-whitespace ASCII
    and Unicode characters except `.;{}()@"`, excluding reserved symbols
    and keywords such as `→` or `where`. Underscores in names play a special role
    for mixfix notation.

Mixfix notation.
:   Agda supports *mixfix notation* for defining operators, with
    underscores in the name of a symbol indicating argument positions.
    For example, if we declare `_+_ : Nat → Nat → Nat`,
    we can use it as `1 + 1` (the spaces are required, since `1+1` is a valid Agda name!).

Anonymous functions.
:   Lambda abstractions use the syntax `λ x → u` instead of `λ x. u`.

Implicit arguments.
:   Arguments marked by single curly braces `{…}` in the type of a symbol are
    considered to be *implicit*. These arguments may be omitted, and are
    then inferred by Agda's type checker.

Type classes.
:   Agda has no direct support for type classes, but they can be
    simulated using Agda's *instance arguments* to resolve type class
    instances. Instance arguments are marked by double curly braces `{{…}}` and
    are resolved automatically by using definitions marked as `instance`.

Rewrite rules.
:   Agda has support for *rewrite rules* [(Cockx2020TTU)]
    that are applied automatically during type checking. Rewrite rules
    are declared by marking an equality proof 
    `eq : a ≡ b` with a `{-# REWRITE eq #-}` pragma. Agda can
    optionally check confluence of rewrite rules, but currently does not
    check their termination. Since only *proven* (or postulated)
    equalities can be added as rewrite rules, non-confluence and
    non-termination cannot affect the soundness of Agda's type checker,
    only its completeness [(Cockx2021TRT)].

[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf
[(Agda-Language)]: https://agda.readthedocs.io/en/v2.8.0/language/
[(Agda-Wikipedia)]: https://en.wikipedia.org/wiki/Agda_(programming_language)
[(Cockx2021TRT)]: https://doi.org/10.1145/3434341
[(Cockx2020TTU)]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2019.2
[(Reynolds1998TPL)]: https://doi.org/10.1017/CBO9780511626364
[(Scheme)]: https://standards.scheme.org
[(Scott1970OMT)]: https://ncatlab.org/nlab/files/Scott-TheoryOfComputation.pdf
[(Scott1972CL)]: https://doi.org/10.1007/BFb0073967
[(Stoy1977DSS)]: https://mitpress.mit.edu/9780262690768/denotational-semantics/
[(Tennent1976DSP)]: https://doi.org/10.1145/360303.360308