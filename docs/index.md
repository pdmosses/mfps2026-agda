# Mechanising Denotational Semantics in Agda

## Abstract

Mechanisation of a mathematical definition (also referred to as formalisation)
has many benefits. Here, we focus on mechanising denotational semantic definitions
of programming languages by embedding them in the Agda language. The Agda
type-checker detects and reports any issues with the wellformedness and type
correctness of the embedded definitions.

To minimise the effort required, and to facilitate correlation of the original
definition with its Agda embedding, mechanisation should not involve significant
reformulation or extension. Here, we show how  to embed conventional Scott–Strachey
denotational definitions in Agda with almost no changes to $\lambda$-notation or
domain equations.

Agda notation for definitions of types and functions corresponds closely
to the conventional meta-notation of denotational semantics. We have developed
a collection of Agda modules with postulated types for commonly used domain
constructors and their associated operations. Some of our postulates are
inconsistent with a classical set-theoretic interpretation of Agda; we conjecture
that they would be consistent with an interpretation of Agda in the higher-order
intuititionistic logic used by Simpson in his work on synthetic domain theory.

We illustrate our approach with mechanisations of three denotational definitions:
Scott’s $D_\infty$ model of the untyped $\lambda$-calculus, Plotkin’s denotational
semantics of PCF, and a semantics of a sublanguage of Scheme. In previous work,
similar mechanisations in Agda have revealed several unsuspected wellformedness
issues in published denotational definitions.

## Discussion

Advice and suggestions are welcome, e.g., by posting to the repo [Discussions].

Peter Mosses <p.d.mosses@tudelft.nl>

[LC]: Examples/LC/index.md
[PCF]: Examples/PCF/index.md
[Scm]: Examples/Scm/index.md
[Notation]: Notation.md
[Properties]: Properties.md

[Scheme]: https://scheme.org
[Formalizing Synthetic Domain Theory]: https://doi.org/10.1023/A:1006258506401
[Lego]: https://www.dcs.ed.ac.uk/home/lego/
[Computational adequacy for recursive types in models of intuitionistic set theory]: https://doi.org/10.1016/j.apal.2003.12.005
[Discussions]: https://github.com/pdmosses/xds-agda/discussions