# Illustrative Tests

The tests below illustrate *automatic* proof by the Agda type-checker that
the denotations of some terms compute the expected values.
The type-correctness of the `refl` definitions of the declared equivalences
confirms that they hold.

Apart from confirming that a denotational semantics defines denotations
which compute the expected values at least for some terms,
the tests also depend on the imported rewrite rules for [postulated properties].
The success of those tests indirectly checks that the rewrite rules preserve denotations.
(A more systematic approach would be to develop a suite of unit tests for consequences
of postulated properties, independently of denotational definitions.)

[Postulated Properties]: ../Properties/index.md#postulated-properties


```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

module Tests where

  import Tests.LC
  import Tests.PCF
  import Tests.Scm
--"/hide"
```