# Untyped λ-calculus

This section presents an Agda formalisation of a denotational semantics
of the untyped $\lambda$-calculus.
Elided module imports are shown in the complete code [(MFPS2026-Agda)].
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.LC where

import Examples.LC.Abstract-Syntax
import Examples.LC.Domain-Equations
import Examples.LC.Semantic-Functions
--"/hide"
```
See the [Tests] module for some examples of abstract syntax terms and
equivalence proofs.

[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/
[Tests]: ../../Tests/LC.md