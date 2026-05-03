# Untyped λ-calculus

The language `LC` corresponds to the untyped call-by-name λ-calculus.
The syntax of terms and the conversion rules of the calculus were defined by
Alonzo Church in 1936. A domain $D_\infty$ isomorphic to a space of
endofunctions on $D_\infty$ was defined by Dana Scott in 1969, and used to
give a model of the calculus (with combinators instead of λ-abstractions).

[LC.Definitions] is a shallow embedding of a conventional denotational
semantics of `LC`. It illustrates how to postulate a domain `D∞`, together with
inverse functions between `D∞` and a domain of endofunctions on `D∞`, using the
notatation declared in the [Notation] module.

[LC.Tests] declares some equivalence assertions about term denotations,
and proves that they hold. 

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module LC where

import LC.Definitions
import LC.Tests
```

[LC.Definitions]: Definitions.md
[LC.Tests]: Tests.md
[Notation]: ../Notation.md