# Illustrative Tests

The tests below illustrate *automatic* proof by the Agda type-checker that
the denotations of some terms compute the expected values.
The type-correctness of the `refl` definitions of the declared equivalences
confirms that they hold.

Apart from confirming that a denotational semantics defines denotations
which compute the expected values at least for some terms,
the tests also depend on the imported rewrite rules for [postulated properties].
The success of those tests indirectly checks that the rewrite rules preserve denotations.
(A more systematic approach would be to develop a suite of unit tests for consequences of postulated properties,
independently of denotational definitions that use the involved operations.)
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Tests where
  import Tests.LC
  import Tests.PCF
```

We leave development of significant tests for the `Scm` language to future work.
This is partly because the published denotational definition of *Scm* [(Mosses2025CDS)]
leaves various domains and operations unspecified, and our Agda embedding merely postulates them;
denotations that involve operations on postulated domains do not (in general)
compute particular elements of domains.
The Agda type-checker can reduce the embeddings of denotation terms with postulated operation
to (weak) head form, thereby testing the properties that we have declared as rewrite rules.

As a workaround, we could replace the embedded declarations of the postulated domains and operations
by definitions; e.g., the postulated type `Loc` of locations could be defined by `Loc = Nat`,
and the postulated operation `new` could then be defined to give the first location
mapped to `unallocated` by the current store.
But that would undermine the correspondence between the published denotational semantics
and its Agda embedding.

[Postulated Properties]: ../Properties/index.md#postulated-properties
[(Mosses2025CDS)]: https://doi.org/10.1145/3759537.3762694
