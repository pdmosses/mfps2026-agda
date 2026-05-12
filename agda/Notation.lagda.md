# Postulated Domain Notation

This section introduces the Agda module [Notation],[^website]
which declares conventional notation for domain constructors and
the associated functions on their carrier sets.

[Notation]: Notation.md
[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/
[^website]:
    In PDF, references to modules in the text are links to sections of the
    generated website that lists all the literate Agda modules
    [(MFPS2026-Agda)].

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Notation where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite using ()
open import Agda.Builtin.Nat public using (Nat) renaming (_==_ to _==ᴺ_) 

variable A B C : Set
--"/hide"
```

## Domains

Domains are elements of the Agda type `Domain`.
A domain `D` is not itself a type,
but it has a carrier type `⟪ D ⟫`,
which always contains an element `⊥`.
(Agda can usually infer the domains in $\lambda$-notation,
so `D` is declared as an implicit argument of `⊥`.)
```agda
module Domains where
  postulate
    Domain : Set              -- Domain is the type of all domains
    ⟪_⟫ : Domain → Set        -- ⟪ D ⟫ is the type of elements of D
    ⊥ : {D : Domain} → ⟪ D ⟫  -- ⊥{D} is the bottom element of D
--"hide"
    𝟙 : Domain                -- 𝟙 is a unit domain
  variable D E F : Domain

open Domains public
--"/hide"
```
In three previous papers based on denotational semantics in Agda,
[(Mosses2025CDS)],
[(Mosses2025CSE)],
[(Mosses2025LAF)],
the type of domains was defined by `Domain = Set`. However,
postulating `⊥ : D` for all domains `D` was then
*inconsistent* with the existence of an empty type in Agda. The
current declaration `Domain : Set` circumvents that issue, but
domains `D` now need to be distinguished from their
carrier sets `⟪ D ⟫`.

The specified postulates that declare types and functions
for domains are used only for type-checking denotational semantics in
Agda. They do *not* define the conventional mathematical structure
of domains, nor the algebraic and universal properties of the associated
functions.

[(Mosses2025CDS)]: https://doi.org/10.1145/3759537.3762694
[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[(Mosses2025LAF)]: https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper11.pdf

## Function domains

The conventional notation in denotational definitions for the domain of
all continuous functions from $D$ to $E$ is usually
$D \to E$ or $[D \to E]$.
However, Agda reserves the notation
`D → E` for the *type* of *all* total functions from
`D` to `E`. The following module declares the notation
`D →ᶜ E` for domains of continuous functions.
```agda
module Functions where
  postulate _→ᶜ_ : Domain → Domain → Domain
  -- D →ᶜ E is the domain of continuous functions from D to E
--"hide"
  infixr 0 _→ᶜ_
--"/hide"
```
In conventional denotational semantics, functions between domains are
*automatically* continuous when defined in terms of λ-abstraction
and application from primitive continuous functions associated with
specific domain constructors.
The carrier `⟪ D →ᶜ E ⟫` of a function domain
`D →ᶜ E` should consist of just the (Scott-)continuous
functions between the carriers `⟪ D ⟫` and `⟪ E ⟫`. In
Agda, however, that would require pairing all λ-abstractions with
explicit proofs of their continuity,
which is quite impractical – especially in continuation-passing style.
To support type-checking direct use of conventional λ-notation for defining functions
between domains, the type `⟪ D →ᶜ E ⟫` is
*rewritten* to the Agda type `⟪ D ⟫ → ⟪ E ⟫`:
```agda
  postulate dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}
```
Continuous *endofunctions* `φ` on `D` have
(least) fixed points `fix φ`:
```agda
  postulate fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
  -- fix φ is the least fixed point of the continuous function φ
```
Functions from an ordinary set `A` to a domain `D`
form a domain `A →ˢ D`:
```agda
  postulate _→ˢ_ : Set → Domain → Domain
  -- A →ˢ D is the domain of all functions from A to D
--"hide"
  infixr 0 _→ˢ_
--"/hide"
```
The type `⟪ A →ˢ D ⟫` is *rewritten* to the Agda type `A → ⟪ D ⟫`:
```agda
  postulate set-cts : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}
```
```agda
--"hide"
open Functions public
--"/hide"
```

## Recursive domains

Conventional denotational semantics often involves groups of mutually
recursive domain definitions.
In Agda, recursive type definitions lead to non-termination of
the type-checker.
To avoid non-termination, it is sufficient to break the recursion by
leaving (one or more) domains as *postulated*. The following operations
can then be used to map values from a postulated domain to its structure
and *vice versa* (as in [(Abramsky1995DT)]).
```agda
module Recursion where
  postulate
    _≅_ : Domain → Domain → Set
    -- an instance of D ≅ E declares that the structure of D is the same as E
    unfold :  {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold :    {{D ≅ E}} → ⟪ E →ᶜ D ⟫
```
The *instance parameter* `{{D ≅ E}}` of the above operations restricts them
to domains `D` and `E` such that `instance _ : D ≅ E` has been declared.

[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf

## Flat domains

Lifting an ordinary set $A$ by adding a $\bot$ element gives a flat domain,
usually written $A_\bot$.
The Agda module `Flat` postulates a corresponding domain constructor `A +⊥`,
together with a function `↑` for injecting elements of `A` into `A +⊥`,
and an operator `f ♯` for extending a function `f` on `A`
to a continuous function on `A +⊥`.
```agda
module Flat where
  postulate
    _+⊥  : Set → Domain                 -- A +⊥ constructs a flat domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫              -- (↑ a) injects a into A +⊥
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫  -- f ♯ extends f to map ⊥ to ⊥
```

### Booleans

The McCarthy conditional operation `β ⟶ δ₁ , δ₂` extends the usual ternary
conditional choice to domains. It returns `⊥` whenever its first argument is `⊥`.
```agda
  module Booleans where
--"hide"
    open import Data.Bool.Base public using (Bool; false; true; if_then_else_)
--"/hide"
    Bool⊥ = Bool +⊥
    _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫    -- β ⟶ δ₁ , δ₂ is conditional choice
    _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂)♯  
--"hide"
    infixr 20 _⟶_,_
--"/hide"
```
@omit
The instance parameter of the strict equality test `δ₁ ==⊥ δ₂` below declares
the operation only for flat domains `A +⊥` with `instance _ : Eq A`.
(Equality is unavailable on non-flat domains because it is not continuous.)
@/omit
```agda
--"hide"
    record Eq (A : Set) : Set where field _==_ : A → A → Bool
    open Eq {{...}} public
    postulate
      _==⊥_ : {{Eq A}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
      -- δ₁ ==⊥ δ₂ is ⊥ when either operand is ⊥
      instance eqBool : Eq Bool
--"/hide"
```

### Naturals

Agda allows decimal notation for natural numbers, as well as unary notation
using `zero` and `suc`.
```agda
  module Naturals where
--"hide"
    open import Agda.Builtin.Nat public
      using (Nat; suc; _+_; _-_) renaming (_==_ to _==ᴺ_)
--"/hide"
    Nat⊥ = Nat +⊥
--"hide"
    open Booleans
    postulate 
      instance eqNat : Eq Nat
--"/hide"
```

## Sum domains

The separated sum `D + E` of two domains corresponds to lifting the disjoint
union of their carrier sets. 
The following operations can be used directly for binary sums,
and iterated for domains with more than two summands.
```agda
module Sums where
  postulate
    _+_    : Domain → Domain → Domain   -- D + E is separated sum
    inj₁   : ⟪ D →ᶜ (D + E) ⟫           -- inj₁ δ is injection from D
    inj₂   : ⟪ E →ᶜ (D + E) ⟫           -- inj₂ ε is injection from E
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ ((D + E) →ᶜ F) ⟫
    -- [ φ , ψ ] applies φ to arguments in D, and ψ to arguments in E
```
Agda also supports type-checking the notation explained in §2.1.
However, instead of defining the summands `D` of a separated sum
domain `E` by an equation `E = ... + D + ...`, the
domain `E` is merely \emph{postulated}, and each summand is
declared separately by `instance \_ : E ≳ n ↦ D` (where
`n` should be a different natural number for each summand).
The inherently \emph{dependent} types of the summand operations are as
follows.
```agda
--"hide"
  open import Agda.Builtin.Nat using (Nat)
  open Flat
  open Flat.Booleans
  open Flat.Naturals
  variable n : Nat
--"/hide"
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫      -- δ in⊥ E injection
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫      -- ε |⊥ D  projection
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫  -- ε ∈⊥ D  test
```

## Product domains

The carrier of the binary cartesian product of two domains consists of all
pairs of elements of the carriers of the agument domains. Neither the product
nor pairing is associative. The following operations can be used directly for
binary products, and iterated for products of more than two domains.
```agda
module Products where
  postulate
    _×_  : Domain → Domain → Domain  -- D × E is cartesian product
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫     -- (δ , ε) is a pair of elements
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫          -- (δ , ε)↓₁ is δ
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫          -- (δ , ε)↓₂ is ε
--"hide"
  infixr 2 _×_
  infixr 4 _,_
--"/hide"
```
The complete Agda code also declares notation for tuple domains `D ^ n` and
sequence domains `D ⋆` corresponding closely to that summarised in §2.1.

### Tuples

The domain `D ^ n` of `n`-tuples of elements of a domain `D` is conventionally
written $D^n$, but Agda does not support the use of variables as superscripts.
```agda
  module Tuples where
--"hide"
    open import Agda.Builtin.Nat public using (Nat; suc)
--"/hide"
    _^_ : Domain → Nat → Domain         -- D ^ n is the domain of n-tuples (n ≥ 0)
--"hide"
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)
--"/hide"
```
@omit
Making `D ^ 2` definitionally equal to `D × D` in Agda supports type-checking
the conventional notational ambiguity between tuples and iterated products.
@/omit

### Sequences

The domain `D ⋆` of finite sequences of elements of a domain `D` is
conventionally written $D^*$.

The following notation for the various operations on sequences was introduced
and extensively used by Strachey and his colleagues in the early 1970s.
(The single angle-brackets `⟨...⟩` used to form sequences are unrelated to the
double angle-brackets `⟪ D ⟫` used for the carrier of domain `D`.)
```agda
  module Sequences where
--"hide"
    open Flat.Naturals
    open Tuples
    variable n : Nat
--"/hide"
    postulate
      _⋆     : Domain → Domain          -- D ⋆ is the finite sequence domain
      ⟨⟩     : ⟪ D ⋆ ⟫                  -- ⟨⟩ is the empty sequence
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫   -- ⟨ δ₁ , ... ⟩ is a non-empty sequence
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫          -- # δ⋆ is the length of sequence δ⋆
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫    -- δ⋆₁ § δ⋆₂ is sequence concatenation
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫      -- δ⋆ ↓ n is the nth element
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫    -- δ⋆ † n is the nth tail
```

## Updates

When an ordinary Agda type `A` has an equality operation `_==_ : A → A → Bool`,
environments `ρ : ⟪ A →ˢ D ⟫` can be 'updated' (i.e., extended or overridden) using the
conventional notation `ρ [ δ / a ]`, defined as follows.
```agda
module Updates where
--"hide"
  open Flat
  open Flat.Booleans
--"/hide"
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
  -- ρ [ δ / a ] maps a to δ, and other arguments a′ to ρ a′
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′
```
Similarly for stores `σ : ⟪ (A +⊥) →ᶜ D ⟫`:
```agda
--"hide"
  open Flat
--"/hide"
  _[_/_]⊥ : {{Eq A}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
  -- σ [ δ / α ]⊥ maps α to δ, and other arguments α′ to σ α′
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′
```
Defining extension or overriding of *dependent* maps is less straightforward,
as it involves a function that returns an *equivalence proof* instead of a
truth value.
```agda
--"hide"
  open import Data.Maybe.Base public using (Maybe; just; nothing)
  open import Relation.Binary.PropositionalEquality.Core public using (_≡_; refl)
  record MaybeEq (A : Set) : Set where field _==?_ : (a a′ : A) → Maybe (a ≡ a′)
  open MaybeEq {{...}} public
  variable X : Set; Y : X → Set
  _[_←_] :  {{MaybeEq X}} → (∀ x′ → Y x′) → (x : X) → Y x → (∀ x′ → Y x′)
  _[_←_] {X} {Y} m x y = λ x′ → h x′ (x ==? x′) where
    h : (x′ : X) → Maybe (x ≡ x′) → Y x′
    h x′ (just refl) = y
    h x′ nothing = m x′
--"/hide"
```