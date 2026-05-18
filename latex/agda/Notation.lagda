\section{Postulated Domain Notation}\label{Notation-postulated-domain-notation}

This section postulates Agda notation for the domain constructors and
associated functions used in the
illustrative examples (Section~\ref{Examples-illustrative-examples}\,\href{https://pdmosses.github.io/mfps2026-agda/Examples/\#illustrative-examples}{$\Uparrow$}).
 See the accompanying website
\cite{MFPS2026-Agda} for
hyperlinked, highlighted listings of the complete Agda code with the
details elided here (including module imports, fixity declarations, and
declarations of the types of meta-variables). In the PDF, the symbol
\(\Uparrow\) following a reference to a numbered section is a link to
the corresponding page on the website. 
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Notation where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite using ()
open import Agda.Builtin.Nat public using (Nat) renaming (_==_ to _==ᴺ_) 

variable A B C : Set
\end{code}
\end{AgdaSuppressSpace}
%
\subsection{Domains}\label{Notation-domains}

Domains are embedded in Agda as elements of the type \AgdaRef{Domain}. A
domain \AgdaRef{D} is not itself a type, but it has a \emph{carrier} type
\AgdaRef{⟪\ D\ ⟫\ :\ Set}, which always contains an element
\AgdaRef{⊥\{D\}} (written \AgdaRef{⊥} when Agda can infer \AgdaRef{D}).
%
\begin{AgdaSuppressSpace}
\begin{code}
module Domains where
  postulate
    Domain : Set              -- Domain is the type of all domains
    ⟪_⟫ : Domain → Set        -- ⟪ D ⟫ is the carrier type of D
    ⊥ : {D : Domain} → ⟪ D ⟫  -- ⊥{D} is the 'bottom' element of D
\end{code}
\begin{code}[hide]
    𝟙 : Domain                -- 𝟙 is a unit domain
  variable D E F : Domain

open Domains public
\end{code}
\end{AgdaSuppressSpace}
%
Some previous papers on embedding denotational semantics in Agda
\cite{Mosses2025CDS,Mosses2025CSE,Mosses2025LAF}
defined domains to be types: \AgdaRef{Domain\ =\ Set}. However,
postulating \AgdaRef{⊥\ :\ D} for all \AgdaRef{D\ :\ Domain} was then
\emph{inconsistent} with the existence of an empty type in Agda.
Postulating \AgdaRef{Domain\ :\ Set} avoids that inconsistency.

The notation for domains postulated here supports \emph{type-checking}
embeddings of denotational semantics in Agda such as those in the
illustrative examples. It does \emph{not} define or constrain the
\emph{mathematical structure} of domains, nor the algebraic and
universal properties of the associated functions.

\subsection{Function Domains}\label{Notation-function-domains}

The conventional notation in denotational definitions for the domain of
continuous functions from \(D\) to \(E\) is \(D \to E\) or
\([D \to E]\). However, Agda reserves the notation \AgdaRef{D\ →\ E} for
the \emph{type} of \emph{all} (total) functions from type \AgdaRef{D} to
type \AgdaRef{E}; instead, we use the notation \AgdaRef{D\ →ᶜ\ E} for
embedding continuous function domains:
%
\begin{AgdaSuppressSpace}
\begin{code}
module Functions where
  postulate _→ᶜ_ : Domain → Domain → Domain
\end{code}
\begin{code}[hide]
  -- D →ᶜ E is the domain of continuous functions from D to E
  infixr 0 _→ᶜ_
\end{code}
\end{AgdaSuppressSpace}
%
Both λ-abstraction and application preserve continuity. In conventional
denotational semantics, functions between domains are defined using
λ-abstraction and application from primitive continuous functions
associated with specific domain constructors, so they are
\emph{automatically} continuous. This motivates treating the carrier
\AgdaRef{⟪\ D\ →ᶜ\ E\ ⟫} of the embedding of a function domain as a type
of continuous functions. (\emph{Proving} functions defined in λ-notation
to be continuous in Agda requires pairing each λ-abstraction with an
explicit proof of its continuity, which is quite impractical --
especially when embedding denotations defined in continuation-passing
style.)

However, to support type-checking the \emph{direct} embedding of
λ-notation from conventional denotational definitions in Agda, it
appears to be necessary to \emph{rewrite} the carrier types of function
domains to ordinary function types:
%
\begin{AgdaSuppressSpace}
\begin{code}
  postulate dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}
\end{code}
\end{AgdaSuppressSpace}
%
Similarly, the notation \AgdaRef{A\ →ˢ\ D} is the embedding of the domain
of all functions from an ordinary type \AgdaRef{A} to a domain \AgdaRef{D}
(which are trivially continuous, ordered pointwise):
%
\begin{AgdaSuppressSpace}
\begin{code}
  postulate _→ˢ_ : Set → Domain → Domain
\end{code}
\begin{code}[hide]
  -- A →ˢ D is the domain of all functions from A to D
  infixr 0 _→ˢ_
\end{code}
\begin{code}
  postulate set-cts  : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}
\end{code}
\end{AgdaSuppressSpace}
%
Embeddings of \emph{endofunctions} \AgdaRef{φ} on a domain \AgdaRef{D}
should always have fixed points \AgdaRef{fix\ φ}, with \AgdaRef{fix}
itself also being continuous:
%
\begin{AgdaSuppressSpace}
\begin{code}
  postulate fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
\end{code}
\end{AgdaSuppressSpace}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
open Functions public
\end{code}
\end{AgdaSuppressSpace}
%
\subsection{Recursive Domains}\label{Notation-recursive-domains}

Conventional denotational semantics often involves groups of mutually
recursive domain definitions. In Agda, recursive type definitions lead
to non-termination of the type-checker. To avoid non-termination, it is
sufficient to break the recursion by leaving (one or more) domains as
\emph{postulated}. The following operations can then be used to map
values from a postulated domain to its structure and \emph{vice versa}.
%
\begin{AgdaSuppressSpace}
\begin{code}
module Recursion where
  postulate
    _≅_ : Domain → Domain → Set
    -- an instance of D ≅ E declares that the structure of D is the same as E
    unfold  : {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold    : {{D ≅ E}} → ⟪ E →ᶜ D ⟫
\end{code}
\end{AgdaSuppressSpace}
%
The \emph{instance parameter} \AgdaRef{\{\{D\ ≅\ E\}\}} of the above
operations restricts them to domains \AgdaRef{D} and \AgdaRef{E} for which
\AgdaRef{instance\ \_\ :\ D\ ≅\ E} has been declared.

\subsection{Flat Domains}\label{Notation-flat-domains}

Lifting an ordinary set \(A\) by adding a \(\bot\) element gives a flat
domain, usually written \(A_\bot\). Our Agda embedding postulates a
corresponding domain constructor \AgdaRef{A\ +⊥}, together with a
function \AgdaRef{↑} for injecting elements of \AgdaRef{A} into
\AgdaRef{A\ +⊥}, and an operator \AgdaRef{f\ ♯} for extending functions on
\AgdaRef{A} to arguments in \AgdaRef{A\ +⊥}.
%
\begin{AgdaSuppressSpace}
\begin{code}
module Flat where
  postulate
    _+⊥  : Set → Domain                 -- A +⊥ constructs a flat domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫              -- (↑ a) injects a into A +⊥
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫  -- f ♯ extends f to map ⊥ to ⊥
\end{code}
\end{AgdaSuppressSpace}
%
\subsubsection{Booleans}\label{Notation-booleans}

The McCarthy conditional operation \AgdaRef{β\ ⟶\ δ₁\ ,\ δ₂} extends the
usual ternary conditional choice to domains. It returns \AgdaRef{⊥}
whenever its first argument is \AgdaRef{⊥}.
%
\begin{AgdaSuppressSpace}
\begin{code}
  module Booleans where
\end{code}
\begin{code}[hide]
    open import Data.Bool.Base public using (Bool; false; true; if_then_else_)
\end{code}
\begin{code}
    Bool⊥ = Bool +⊥
    _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫    -- β ⟶ δ₁ , δ₂ is conditional choice
    _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂) ♯  
\end{code}
\begin{code}[hide]
    infixr 20 _⟶_,_
\end{code}
\end{AgdaSuppressSpace}
%
This module also defines \AgdaRef{Eq\ A} for use as an instance
parameter, restricting operation definitions to types \AgdaRef{A} such
that \AgdaRef{\_==\_\ :\ A\ →\ A\ →\ Bool}, and postulates a
\AgdaRef{Bool⊥}-valued operation \AgdaRef{δ₁\ ==⊥\ δ₂} on \AgdaRef{A\ +⊥}.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
    record Eq (A : Set) : Set where field _==_ : A → A → Bool
    open Eq {{...}} public
    postulate
      _==⊥_ : {{Eq A}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
      -- δ₁ ==⊥ δ₂ is ⊥ when either operand is ⊥
      instance eqBool : Eq Bool
\end{code}
\end{AgdaSuppressSpace}
%
\subsubsection{Naturals}\label{Notation-naturals}

Agda allows decimal notation for natural numbers, as well as unary
notation using \AgdaRef{zero} and \AgdaRef{suc}.
%
\begin{AgdaSuppressSpace}
\begin{code}
  module Naturals where
\end{code}
\begin{code}[hide]
    open import Agda.Builtin.Nat public
      using (Nat; suc; _+_; _-_) renaming (_==_ to _==ᴺ_)
\end{code}
\begin{code}
    Nat⊥ = Nat +⊥
\end{code}
\begin{code}[hide]
    open Booleans
    postulate 
      instance eqNat : Eq Nat
\end{code}
\end{AgdaSuppressSpace}
%
\subsection{Sum Domains}\label{Notation-sum-domains}

The separated sum \AgdaRef{D\ +\ E} of two domains corresponds to lifting
the disjoint union of their carrier sets. The following operations can
be used directly for binary sums, and iterated for domains with more
than two summands.
%
\begin{AgdaSuppressSpace}
\begin{code}
module Sums where
  postulate
    _+_    : Domain → Domain → Domain   -- D + E is separated sum
    inj₁   : ⟪ D →ᶜ (D + E) ⟫           -- inj₁ δ is injection from D
    inj₂   : ⟪ E →ᶜ (D + E) ⟫           -- inj₂ ε is injection from E
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ ((D + E) →ᶜ F) ⟫
    -- [ φ , ψ ] applies φ to arguments in D, and ψ to arguments in E
\end{code}
\end{AgdaSuppressSpace}
%
Conventional denotational definitions of programming languages (e.g., in
\cite{Scheme}) use domain names instead
of numerical indices in operations associated with separated sums. The
inherently \emph{dependent} types of the Agda embedding of these
operations are as follows.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
  open import Agda.Builtin.Nat using (Nat)
  open Flat
  open Flat.Booleans
  open Flat.Naturals
  variable n : Nat
\end{code}
\begin{code}
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫      -- δ in⊥ E injection
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫      -- ε |⊥ D  projection
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫  -- ε ∈⊥ D  inspection
\end{code}
\end{AgdaSuppressSpace}
%
The operations are defined only for \AgdaRef{D} and \AgdaRef{E} where an
instance of type \AgdaRef{E\ ≳\ n\ ↦\ D} is declared for some \AgdaRef{n}.
Instead of defining the summands \AgdaRef{D} of a separated sum domain
\AgdaRef{E} by an equation \AgdaRef{E\ =\ ...\ +\ D\ +\ ...}, the domain
\AgdaRef{E} is merely \emph{postulated}, and each summand is declared
separately by \AgdaRef{instance\ \_\ :\ E\ ≳\ n\ ↦\ D} (where \AgdaRef{n}
should be a different natural number for each summand).

\subsection{Product Domains}\label{Notation-product-domains}

The carrier of the binary product \AgdaRef{D\ ×\ E} of two domains
consists of all pairs \AgdaRef{(d\ ,\ e)} of elements of \AgdaRef{D} and
\AgdaRef{E} with the pair \AgdaRef{(⊥\{D\}\ ,\ ⊥\{E\})} as the bottom
element \AgdaRef{⊥\{D\ ×\ E\}}. Neither the product nor pairing is
associative. The following operations can be used directly for binary
products, and iterated for products of more than two domains.
%
\begin{AgdaSuppressSpace}
\begin{code}
module Products where
  postulate
    _×_  : Domain → Domain → Domain     -- D × E is cartesian product
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫        -- (δ , ε) is a pair of elements
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫             -- (δ , ε)↓₁ is δ
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫             -- (δ , ε)↓₂ is ε
\end{code}
\begin{code}[hide]
  infixr 2 _×_
  infixr 4 _,_
\end{code}
\end{AgdaSuppressSpace}
%
\subsubsection{Tuples}\label{Notation-tuples}

The domain \AgdaRef{D\ \^{}\ n} of \AgdaRef{n}-tuples of elements of a
domain \AgdaRef{D} is conventionally written \(D^n\), but Agda does not
support the use of variables as superscripts.
%
\begin{AgdaSuppressSpace}
\begin{code}
  module Tuples where
\end{code}
\begin{code}[hide]
    open import Agda.Builtin.Nat public using (Nat; suc)
\end{code}
\begin{code}
    _^_ : Domain → Nat → Domain         -- D ^ n is the domain of n-tuples (n ≥ 0)
\end{code}
\begin{code}[hide]
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)
\end{code}
\end{AgdaSuppressSpace}
%
\subsubsection{Sequences}\label{Notation-sequences}

The domain \AgdaRef{D\ ⋆} of finite sequences of elements of a domain
\AgdaRef{D} is conventionally written \(D^*\).

The following notation for the various operations on sequences was
introduced in the early 1970s, and is used in the \emph{Scheme}
semantics \cite{Scheme}. (The single
angle-brackets \AgdaRef{⟨...⟩} used to form sequences are unrelated to
the double angle-brackets \AgdaRef{⟪\ D\ ⟫} used for the carrier of
domain \AgdaRef{D}.)
%
\begin{AgdaSuppressSpace}
\begin{code}
  module Sequences where
\end{code}
\begin{code}[hide]
    open Flat.Naturals
    open Tuples
    variable n : Nat
\end{code}
\begin{code}
    postulate
      _⋆     : Domain → Domain          -- D ⋆ is the finite sequence domain
      ⟨⟩     : ⟪ D ⋆ ⟫                  -- ⟨⟩ is the empty sequence
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫   -- ⟨ δ₁ , ... ⟩ is a non-empty sequence
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫          -- # δ⋆ is the length of sequence δ⋆
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫    -- δ⋆₁ § δ⋆₂ is sequence concatenation
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫      -- δ⋆ ↓ n is the nth element
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫    -- δ⋆ † n is the nth tail
\end{code}
\end{AgdaSuppressSpace}
%
\subsection{Updates}\label{Notation-updates}

When a type \AgdaRef{A} has an equality operation
\AgdaRef{\_==\_\ :\ A\ →\ A\ →\ Bool}, environments
\AgdaRef{ρ\ :\ ⟪\ A\ →ˢ\ D\ ⟫} can be `updated' (i.e., extended or
overridden) using the conventional notation
\AgdaRef{ρ\ {[}\ δ\ /\ a\ {]}}, defined as follows.
%
\begin{AgdaSuppressSpace}
\begin{code}
module Updates where
\end{code}
\begin{code}[hide]
  open Flat
  open Flat.Booleans
\end{code}
\begin{code}
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
\end{code}
\begin{code}[hide]
  -- ρ [ δ / a ] maps a to δ, and other arguments a′ to ρ a′
\end{code}
\begin{code}
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′
\end{code}
\end{AgdaSuppressSpace}
%
Similarly for stores \AgdaRef{σ\ :\ ⟪\ (A\ +⊥)\ →ᶜ\ D\ ⟫}:
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
  open Flat
\end{code}
\begin{code}
  _[_/_]⊥ : {{Eq A}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
\end{code}
\begin{code}[hide]
  -- σ [ δ / α ]⊥ maps α to δ, and other arguments α′ to σ α′
\end{code}
\begin{code}
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′
\end{code}
\end{AgdaSuppressSpace}
%
Defining an operation \AgdaRef{m\ {[}\ x\ ←\ y\ {]}} for extension or
overriding of \emph{dependent} maps \AgdaRef{m} is less straightforward,
as it involves an equality test that may return an \emph{equivalence
proof}.
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
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
\end{code}
\end{AgdaSuppressSpace}
