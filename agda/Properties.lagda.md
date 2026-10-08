# Postulated Properties

the [postulated domain notation] declares domain constructors and their associated operations,
which we use in our embedding of conventional denotational semantic definitions in Agda.
The `Properties` modules postulate basic properties of some of the associated operations.
These properties are expected to hold in various categories of domains,
but they do *not* define the *mathematical structure* of domains.

The postulated properties support proofs that denotations compute the expected values
When postulated properties are declared as *rewrite rules*,
Agda can use them *automatically* in proofs.
Agda also has an option to check that the declared rewrite rules form a confluent system.
Rewrite rules are safe to use with `Agda.Builtin.Equality` when that option is enabled.
Confluent but non-terminating rewrite rules cannot break consistency
[(Cockx2021TRT)].
The rewrite rules declared in the modules imported below support *automatic* proof
of all the illustrative tests: the proof terms are simply `refl` (i.e., reflexivity).
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Properties where
  import Properties.Functions
  import Properties.Flat
  import Properties.Sums
  import Properties.Recursion
```
Removing any of the rewrite rules in the above modules
breaks the proof in at least one of the illustrative tests.
In principle, all `refl` proof terms that rely on rewrite rules could be replaced by proofs
that apply the postulated properties to specified subterms.
However, we expect that it would be quite tedious to develop such proofs,
and reading them is unlikely to provide new insights.

The postulated properties in the remaining modules are for domains that are not used
in the semantics of the LC and PCF languages;
they will be needed when tests for equivalence of denotations of *Scm* expressions are added.
Postulates of properties for the operations on tuples and sequences have not yet been developed.
```agda
--"hide"
  import Properties.Flat.Booleans
  import Properties.Flat.Naturals
  import Properties.Products
  import Properties.Products.Tuples
  import Properties.Products.Sequences
  import Properties.Updates
--"/hide"
```

[Postulated Domain Notation]: ../Notation/index.md#postulated-domain-notation
[Illustrative Tests]: ../Tests/index.md#illustrative-tests
[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf
[(Cockx2021TRT)]: https://doi.org/10.1145/3434341
