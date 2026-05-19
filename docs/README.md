# Mechanising Denotational Semantics in Agda

Code repository accompanying a paper ([PDF]) to be [presented] at [MFPS 2026]:

> Peter D. Mosses, Jesper Cockx, Bernhard Reus: *Mechanising Denotational Semantics in Agda*

[PDF]: https://ul-fmf.github.io/mfps-sstt-2026/files/pdfs/mfps/MFPS26-17.pdf
[presented]: https://ul-fmf.github.io/mfps-sstt-2026/programme/#wednesday-june-3-mfps
[MFPS 2026]: https://ul-fmf.github.io/mfps-sstt-2026/mfps/

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

## Contributing

Please report any [issues] that you notice.

Comments and suggestions for improvement are welcome, and can be added as [Discussions].

## Contact

Peter Mosses

[p.d.mosses@tudelft.nl](mailto:p.d.mosses@tudelft.nl)

[pdmosses.github.io](https://pdmosses.github.io)

[Issues]: https://github.com/pdmosses/mfps2026-agda/issues
[Pull requests]: https://github.com/pdmosses/mfps2026-agda/pulls
[Discussions]: https://github.com/pdmosses/mfps2026-agda/discussions