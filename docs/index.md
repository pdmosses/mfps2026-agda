# About this website

> Experiments with Agda support for Scott–Strachey denotational semantics

## Illustrative Examples

Complete examples of denotational semantics definitions in Agda:

- [LC]: the untyped λ-calculus
- [PCF]: an intrinsically (simply) typed programming language based on LCF.[^1]
- [Scm]: a sublanguage of [Scheme]

[^1]: LCF is Scott's logic of computable functions.

## Domains in Denotational Semantics

In the Scott–Strachey style of denotational semantics:

- types of denotations are (Scott-)domains;
- domains are cpos with least elements, and can be defined recursively;
- denotations are defined in λ-notation, and functions are continuous;
- the isomorphisms between domains and their definitions are left implicit.

## Postulating Domains in Agda

The purpose of this repository is to experiment with defining denotational
semantics straightforwardly in Agda.

The current examples use *postulated* domain constructors and
associated operations declared in the [Notation] module and its submodules.
Some of the postulates are inconsistent with a classical set-theoretic
interpretation of Agda.

The `Tests` modules use the postulated equivalences and rewrite rules for the
associated operations declared in the [Properties] module and its submodules.

### Implementing Synthetic Domain Theory in Agda

An implementation of *Synthetic Domain Theory* (SDT) in Agda would allow
domain constructors and associated operations to be defined from a smaller
collection of postulates that are known to have a model.

From the abstract of [Formalizing Synthetic Domain Theory] by Bernhard Reus
(J. Automated Reasoning, 1999):

> Synthetic Domain Theory (SDT) is a constructive variant of Domain Theory
> where all functions are continuous following Dana Scott’s idea of
> “domains as sets”.
> 
> In this article a logical and axiomatic version of SDT capturing the essence
> of Domain Theory à la Scott is presented. It is based on a sufficiently
> expressive version of constructive type theory and fully implemented in the
> proof checker [Lego].

It appears that the implementation uses impredicativity and proof-irrelevance,
which may prevent migration to Agda.

From the abstract of
[Computational adequacy for recursive types in models of intuitionistic set theory]
by Alex Simpson (Ann. Pure and Applied Logic, 2004):

> This paper provides a unifying axiomatic account of the interpretation of
> recursive types that incorporates both domain-theoretic and realizability
> models as concrete instances. Our approach is to view such models as full
> subcategories of categorical models of intuitionistic set theory. 

From §3:

> Although in this paper we use models of IZF set theory to achieve algebraic
> compactness, many other set theories and type theories appear rich enough to
> carry out the proofs in this paper. ... In fact, it seems likely that, with
> appropriate reformulations, the development of this paper could be carried
> out in the (predicative) context of Martin-Löf’s Type Theory.

It remains to be seen whether the development can be implemented in Agda...

## Discussion

Advice and suggestions are welcome, e.g., by posting to the repo [Discussions].

Peter Mosses <p.d.mosses@tudelft.nl>

[LC]: Examples/LC/index.md
[PCF]: Examples/PCF/index.md
[Scm]: Examples/Scm/index.md
[Notation]: Notation.md
[Properties]: Properties.md

[Scheme]: https://scheme.org
[Formalizing Synthetic Domain Theory]: https://doi.org/10.1023/A:1006258506401
[Lego]: https://www.dcs.ed.ac.uk/home/lego/
[Computational adequacy for recursive types in models of intuitionistic set theory]: https://doi.org/10.1016/j.apal.2003.12.005
[Discussions]: https://github.com/pdmosses/xds-agda/discussions