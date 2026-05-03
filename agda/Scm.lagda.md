# Scm: A Sublanguage of Scheme

Scm is a particularly basic sublanguage of the core Scheme expressions whose
denotational semantics is defined in the [Scheme reports].

A denotational semantics for Scm is defined in the following paper:

> Peter D. Mosses. 2025. A Compositional Semantics for `eval` in Scheme.
> In *Proceedings of the Workshop Dedicated to Olivier Danvy*
> *on the Occasion of His 64th Birthday (OLIVIERFEST ’25),*
> *October 12–18, 2025, Singapore, Singapore.*
> ACM, New York, NY, USA, 10 pages. [DOI](https://doi.org/10.1145/3759427.3760369)

[Scm] is a shallow embedding of the published denotational definition.

[Scm.Abstract-Syntax] illustrates a simple way to declare phrase types for
finite sequences.

[Scm.Domain-Equations] uses all the domain constructors declared in the module
[Notation]. It illustrates how a group of mutually recursive domains can be
embedded by postulating a domain that corresponds to a separated sum domain.

[Scm.Auxiliary-Functions] embeds definitions of the auxiliary functions used in
[Scm.Semantic-Functions], together with definitions of some functions that
correspond to standard Scheme procedures. The embeddings of most of the
definitions are completely straightforward.

[Scm.Semantic-Functions] embeds the definitions of the semantic functions
without significant notational changes. As in the [Scheme Reports], 
the types of semantic functions are declared before defining the denotations
of phrases, which supports mutual recursion without further ado.

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm where

import Scm.Abstract-Syntax
import Scm.Domain-Equations
import Scm.Semantic-Functions
import Scm.Auxiliary-Functions
```

[Scheme Reports]: https://standards.scheme.org

[Scm.Definitions]: Definitions.md
[Scm.Domain-Equations]: Domain-Equations.md
[Scm.Auxiliary-Functions]: Auxiliary-Functions.md
[Scm.Semantic-Functions]: Semantic-Functions.md
[Notation]: ../Notation.md