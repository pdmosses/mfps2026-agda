# Illustrative Examples

This section illustrates mechanisation of denotational semantics in Agda
with three examples, all using the posulated [Notation] for domains and their
associated operations:
Untyped Lambda-Calculus [LC] (§4.1),
Programming Computable Functions [PCF] (§4.2),
a simple sublanguage [Scm] of Scheme [(Scheme)] (§4.3).
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

import Examples.LC
import Examples.PCF
import Examples.Scm
--"/hide"
```

[Notation]: ../Notation.md
[LC]: LC/index.md
[PCF]: PCF/index.md
[Scm]: Scm/index.md
[(Scheme)]: https://standards.scheme.org