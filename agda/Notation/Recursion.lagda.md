## Recursive Domains

Conventional denotational semantics often involves groups of mutually
recursive domain definitions.
In Agda, recursive type definitions lead to non-termination of
the type-checker.
To avoid non-termination, it is sufficient to break the recursion by
leaving (one or more) domains as *postulated*.
The following operations can then be used to map values from a postulated domain
to its structure and *vice versa*.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Notation.Recursion where
  
  open import Notation.Domains
  open import Notation.Functions

  postulate
    _≅_ : Domain → Domain → Set
    -- an instance of D ≅ E declares that the structure of D is the same as E
    unfold  : {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold    : {{D ≅ E}} → ⟪ E →ᶜ D ⟫
```
The *instance parameter* `{{D ≅ E}}` of the above operations restricts them
to domains `D` and `E` for which `instance _ : D ≅ E` has been declared.

[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf
