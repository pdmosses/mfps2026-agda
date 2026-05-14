# Untyped Lambda-Calculus

This section presents an Agda formalisation of a denotational semantics
of the untyped $\lambda$-calculus.
@latex
Elided module imports are included in the [complete code listing].
@/latex
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.LC where

import Examples.LC.Abstract-Syntax
import Examples.LC.Domain-Equations
import Examples.LC.Semantic-Functions
--"/hide"
```

[complete code listing]: https://pdmosses.github.io/mfps2026-agda/Examples/LC/Domain-Equations/