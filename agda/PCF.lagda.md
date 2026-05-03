# PCF

PCF is a programming language for computable functions, based on LCF,
Dana Scott’s logic of computable functions ([Milner 1973]).

> PCF is a call-by-name simply-typed λ-calculus equipped with one or two base
> types (usually natural numbers and Booleans) and a fixed point combinator.
> In essence, PCF is the simplest lazy, purely functional programming language.
> ([PLS Lab])

PCF and its denotational semantics were orginally defined by Dana Scott in 1969
([Scott 1993]) with combinators (`S`, `K`) instead of λ-abstraction.
Gordon Plotkin subsequently defined a denotational semantics for PCF 
including λ-abstraction ([Plotkin 1977]).

[PCF.Definitions] is a shallow embedding of Plotkin's definitions, using the
notatation declared in the [Notation] module.  It illustrates the use of
dependent types in formalising the semantics of an intrinsically-typed
programming language. This example also exploits Agda’s support for Unicode
symbols to minimise notational differences from Plotkin’s paper.

[PC.Tests] declares some equivalence assertions about term denotations,
and proves that they hold. 

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module PCF where

import PCF.Definitions
import PCF.Tests
```

[Milner 1973]: https://apps.dtic.mil/sti/tr/pdf/AD0758645.pdf
[Plotkin 1977]: https://doi.org/10.1016/0304-3975(77)90044-5
[PLS Lab]: https://www.pls-lab.org/PCF
[Scott 1993]: https://doi.org/10.1016/0304-3975(93)90095-B

[PCF.Definitions]: Definitions.md
[PCF.Tests]: Tests.md
[Notation]: ../Notation.md