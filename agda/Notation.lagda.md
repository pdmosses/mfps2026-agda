# Postulated Domain Notation

This section postulates Agda notation for the domain constructors and
associated functions used in the [illustrative examples].
@latex
See the accompanying website [(MFPS2026-Agda)] for hyperlinked, highlighted
listings of the complete Agda code with the details elided here (including module
imports, fixity declarations, and declarations of the types of meta-variables).
In the PDF, the symbol $\Uparrow$ following a reference to a numbered section
is a link to the corresponding page on the website.
@/latex

[Illustrative Examples]: ../Examples/index.md#illustrative-examples
[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Notation where

  import Notation.Domains
  import Notation.Functions
  import Notation.Recursion
  import Notation.Flat
  import Notation.Flat.Booleans
  import Notation.Flat.Naturals
  import Notation.Sums
  import Notation.Products
  import Notation.Products.Tuples
  import Notation.Products.Sequences
  import Notation.Updates
```
