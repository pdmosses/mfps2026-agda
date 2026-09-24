# Postulated Properties

The `Properties` module postulates basic properties of some of the operations
of the [postulated domain notation].
These properties are expected to hold in various categories of domains [(Abramsky1995DT)]
but they do *not* define the *mathematical structure* of domains.

The postulated properties support proofs that terms have identical denotations.
For example, some [illustrative tests] declare that the denotation of a function application
is equivalent to the denotation of a constant;
other tests declare that particular instances of renaming do not affect denotations.

When postulated properties are declared as *rewrite rules*,
Agda can use them *automatically* in proofs.
Agda also has an option to check that the declared rewrite rules form a confluent system.
Rewrite rules are safe to use with `Agda.Builtin.Equality` when that option is enabled.
Confluent but non-terminating rewrite rules cannot break consistency,
as shown by Cockx, Tabareau, and Winterhalter [(Cockx2021TRT)].

The rewrite rules declared below support *automatic* proof of identity for all the illustrative tests:
the proof terms are simply `refl` (i.e., reflexivity).
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Properties where

  import Properties.Domains
  import Properties.Functions
  import Properties.Recursion
  import Properties.Flat
```
Removing any of the rewrite rules in the modules imported above
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
  import Properties.Flat.Booleans
  import Properties.Flat.Naturals
  import Properties.Sums
  import Properties.Products
  import Properties.Products.Tuples
  import Properties.Products.Sequences
  import Properties.Updates
```

[Postulated Domain Notation]: Notation.md#postulated-domain-notation
[Illustrative Tests]: Tests/index.md#illustrative-tests
[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf
[(Cockx2021TRT)]: https://doi.org/10.1145/3434341
