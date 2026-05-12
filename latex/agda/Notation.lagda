\section{Postulated Domain Notation}\label{agda-Notation-postulated-domain-notation}

This section introduces the Agda module
\href{https://pdmosses.github.io/mfps2026-agda/Notation/}{\AgdaRef{Notation}},\footnote{In PDF, references to modules in
  the text are links to sections of the generated website that lists all
  the literate Agda modules
  \cite{MFPS2026-Agda}.}
which declares conventional notation for domain constructors and the
associated functions on their carrier sets.
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
\subsection{Domains}\label{agda-Notation-domains}

Domains are elements of the Agda type \AgdaRef{Domain}. A domain
\AgdaRef{D} is not itself a type, but it has a carrier type
\AgdaRef{⟪\ D\ ⟫}, which always contains an element \AgdaRef{⊥}. (Agda can
usually infer the domains in \(\lambda\)-notation, so \AgdaRef{D} is
declared as an implicit argument of \AgdaRef{⊥}.)
%
\begin{AgdaSuppressSpace}
\begin{code}
module Domains where
  postulate
    Domain : Set              -- Domain is the type of all domains
    ⟪_⟫ : Domain → Set        -- ⟪ D ⟫ is the type of elements of D
    ⊥ : {D : Domain} → ⟪ D ⟫  -- ⊥{D} is the bottom element of D
    𝟙 : Domain                -- 𝟙 is a unit domain
\end{code}
\begin{code}[hide]
  variable D E F : Domain

open Domains public
\end{code}
\end{AgdaSuppressSpace}
%
In three previous papers based on denotational semantics in Agda,
\cite{Mosses2025CDS},
\cite{Mosses2025CSE},
\cite{Mosses2025LAF},
the type of domains was defined by \AgdaRef{Domain\ =\ Set}. However,
postulating \AgdaRef{⊥\ :\ D} for all domains \AgdaRef{D} was then
\emph{inconsistent} with the existence of an empty type in Agda. The
current declaration \AgdaRef{Domain\ :\ Set} circumvents that issue, but
domains \AgdaRef{D} now need to be distinguished from their carrier sets
\AgdaRef{⟪\ D\ ⟫}.

The specified postulates that declare types and functions for domains
are used only for type-checking denotational semantics in Agda. They do
\emph{not} define the conventional mathematical structure of domains,
nor the algebraic and universal properties of the associated functions.
Postulated equivalences between terms are used for testing denotations
of terms; adding them as rewrite rules allows implicit use in proofs.

\subsection{Function domains}\label{agda-Notation-function-domains}

The conventional notation in denotational definitions for the domain of
all continuous functions from \(D\) to \(E\) is usually \(D \to E\) or
\([D \to E]\). However, Agda reserves the notation \AgdaRef{D\ →\ E} for
the \emph{type} of \emph{all} total functions from \AgdaRef{D} to
\AgdaRef{E}. The following module declares the notation \AgdaRef{D\ →ᶜ\ E}
for domains of continuous functions.
%
\begin{AgdaSuppressSpace}
\begin{code}
module Functions where
  postulate
    _→ᶜ_ : Domain → Domain → Domain
    -- D →ᶜ E is the domain of continuous functions from D to E
\end{code}
\begin{code}[hide]
  infixr 0 _→ᶜ_
\end{code}
\end{AgdaSuppressSpace}
%
In conventional denotational semantics, functions between domains are
\emph{automatically} continuous when defined in terms of λ-abstraction
and application from primitive continuous functions associated with
specific domain constructors. The carrier \AgdaRef{⟪\ D\ →ᶜ\ E\ ⟫} of a
function domain \AgdaRef{D\ →ᶜ\ E} should consist of just the
(Scott-)continuous functions between the carriers \AgdaRef{⟪\ D\ ⟫} and
\AgdaRef{⟪\ E\ ⟫}. In Agda, however, that would require pairing all
λ-abstractions with explicit proofs of their continuity, which is quite
impractical -- especially in continuation-passing style. To support
type-checking direct use of conventional λ-notation for defining
functions between domains, the type \AgdaRef{⟪\ D\ →ᶜ\ E\ ⟫} is
\emph{rewritten} to the Agda type \AgdaRef{⟪\ D\ ⟫\ →\ ⟪\ E\ ⟫}:
%
\begin{AgdaSuppressSpace}
\begin{code}
  postulate
    dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}
\end{code}
\end{AgdaSuppressSpace}
%
Continuous \emph{endofunctions} \AgdaRef{φ} on \AgdaRef{D} have (least)
fixed points \AgdaRef{fix\ φ}:
%
\begin{AgdaSuppressSpace}
\begin{code}
  postulate
    fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
    -- fix φ is the least fixed point of the continuous function φ
\end{code}
\end{AgdaSuppressSpace}
%
Functions from an ordinary set \AgdaRef{A} to a domain \AgdaRef{D} form a
domain \AgdaRef{A\ →ˢ\ D}:
%
\begin{AgdaSuppressSpace}
\begin{code}
  postulate
    _→ˢ_ : Set → Domain → Domain
  -- A →ˢ D is the domain of all functions from A to D
\end{code}
\begin{code}[hide]
  infixr 0 _→ˢ_
\end{code}
\end{AgdaSuppressSpace}
%
The type \AgdaRef{⟪\ A\ →ˢ\ D\ ⟫} is \emph{rewritten} to the Agda type
\AgdaRef{A\ →\ ⟪\ D\ ⟫}:
%
\begin{AgdaSuppressSpace}
\begin{code}
  postulate
    set-cts : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}
\end{code}
\end{AgdaSuppressSpace}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
open Functions public
\end{code}
\end{AgdaSuppressSpace}
%
\subsection{Recursive domains}\label{agda-Notation-recursive-domains}

Conventional denotational semantics often involves groups of mutually
recursive domain definitions. In Agda, recursive type definitions lead
to non-termination of the type-checker. To avoid non-termination, it is
sufficient to break the recursion by leaving (one or more) domains as
\emph{postulated}. The following operations can then be used to map
values from a postulated domain to its structure and \emph{vice versa}
(as in
\cite{Abramsky1995DT}).
%
\begin{AgdaSuppressSpace}
\begin{code}
module Recursion where
  postulate
    _≅_ : Domain → Domain → Set
    -- an instance of D ≅ E declares that the structure of D is the same as E
    unfold :  {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold :    {{D ≅ E}} → ⟪ E →ᶜ D ⟫
\end{code}
\end{AgdaSuppressSpace}
%
The \emph{instance parameter} \AgdaRef{\{\{D\ ≅\ E\}\}} of the above
operations restricts them to domains \AgdaRef{D} and \AgdaRef{E} such that
\AgdaRef{instance\ \_\ :\ D\ ≅\ E} has been declared.

\subsection{Flat domains}\label{agda-Notation-flat-domains}

Lifting an ordinary set \(A\) by adding a \(\bot\) element gives a flat
domain, usually written \(A_\bot\). The Agda module \AgdaRef{Flat}
postulates a corresponding domain constructor \AgdaRef{A\ +⊥}, together
with a function \AgdaRef{↑} for injecting elements of \AgdaRef{A} into
\AgdaRef{A\ +⊥}, and an operator \AgdaRef{f\ ♯} for extending a function
\AgdaRef{f} on \AgdaRef{A} to a continuous function on \AgdaRef{A\ +⊥}.
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
\subsubsection{Booleans}\label{agda-Notation-booleans}

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
    _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂)♯  
\end{code}
\begin{code}[hide]
    infixr 20 _⟶_,_
\end{code}
\end{AgdaSuppressSpace}
%
\begin{comment}
 The instance parameter of the strict equality test
\AgdaRef{δ₁\ ==⊥\ δ₂} below declares the operation only for flat domains
\AgdaRef{A\ +⊥} with \AgdaRef{instance\ \_\ :\ Eq\ A}. (Equality is
unavailable on non-flat domains because it is not continuous.) 
\end{comment}
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
\begin{comment}


\subsubsection{Naturals}\label{agda-Notation-naturals}

Agda allows decimal notation for natural numbers, as well as unary
notation using \AgdaRef{zero} and \AgdaRef{suc}. 
\end{comment}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
  module Naturals where
    open import Agda.Builtin.Nat public
      using (Nat; suc; _+_; _-_) renaming (_==_ to _==ᴺ_)
    Nat⊥ = Nat +⊥
    open Booleans
    postulate 
      instance eqNat : Eq Nat
\end{code}
\end{AgdaSuppressSpace}
%
\subsection{Sum domains}\label{agda-Notation-sum-domains}

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
Agda also supports type-checking the notation explained in §2.1.
However, instead of defining the summands \AgdaRef{D} of a separated sum
domain \AgdaRef{E} by an equation \AgdaRef{E\ =\ ...\ +\ D\ +\ ...}, the
domain \AgdaRef{E} is merely \emph{postulated}, and each summand is
declared separately by
\AgdaRef{instance\ \textbackslash{}\_\ :\ E\ ≳\ n\ ↦\ D} (where
\AgdaRef{n} should be a different natural number for each summand). The
inherently \emph{dependent} types of the summand operations are as
follows.
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
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫  -- ε ∈⊥ D  test
\end{code}
\end{AgdaSuppressSpace}
%
\subsection{Product domains}\label{agda-Notation-product-domains}

The carrier of the binary cartesian product of two domains consists of
all pairs of elements of the carriers of the agument domains. Neither
the product nor pairing is associative. The following operations can be
used directly for binary products, and iterated for products of more
than two domains.
%
\begin{AgdaSuppressSpace}
\begin{code}
module Products where
  postulate
    _×_  : Domain → Domain → Domain  -- D × E is cartesian product
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫     -- (δ , ε) is a pair of elements
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫          -- (δ , ε)↓₁ is δ
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫          -- (δ , ε)↓₂ is ε
\end{code}
\begin{code}[hide]
  infixr 2 _×_
  infixr 4 _,_
\end{code}
\end{AgdaSuppressSpace}
%
The complete Agda code also declares notation for tuple domains
\AgdaRef{D\ \^{}\ n} and sequence domains \AgdaRef{D\ ⋆} corresponding
closely to that summarised in §2.1.

\begin{comment}
 \#\#\# Tuples

The domain \AgdaRef{D\ \^{}\ n} of \AgdaRef{n}-tuples of elements of a
domain \AgdaRef{D} is conventionally written \(D^n\), but Agda does not
support the use of variables as superscripts. 
\end{comment}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
  module Tuples where
    open import Agda.Builtin.Nat public using (Nat; suc)
    _^_ : Domain → Nat → Domain         -- D ^ n is the domain of n-tuples (n ≥ 0)
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)
\end{code}
\end{AgdaSuppressSpace}
%
\begin{comment}
 Making \AgdaRef{D\ \^{}\ 2} definitionally equal to
\AgdaRef{D\ ×\ D} in Agda supports type-checking the conventional
notational ambiguity between tuples and iterated products.

\subsubsection{Sequences}\label{agda-Notation-sequences}

The domain \AgdaRef{D\ ⋆} of finite sequences of elements of a domain
\AgdaRef{D} is conventionally written \(D^*\).

The following notation for the various operations on sequences was
introduced and extensively used by Strachey and his colleagues in the
early 1970s. (The single angle-brackets \AgdaRef{⟨...⟩} used to form
sequences are unrelated to the double angle-brackets \AgdaRef{⟪\ D\ ⟫}
used for the carrier of domain \AgdaRef{D}.) 
\end{comment}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
  module Sequences where
    open Flat.Naturals
    open Tuples
    variable n : Nat
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
\subsection{Updates}\label{agda-Notation-updates}

Environments \AgdaRef{ρ\ :\ ⟪\ A\ →ˢ\ D\ ⟫} can be `updated' (i.e.,
extended or overridden) using the conventional notation
\AgdaRef{ρ\ {[}\ δ\ /\ a\ {]}}; stores
\AgdaRef{σ\ :\ ⟪\ (A\ +⊥)\ →ᶜ\ D\ ⟫} use the notation
\AgdaRef{σ\ {[}\ δ\ /\ α\ {]}⊥} for updates. The complete Agda code
\cite{MFPS2026-Agda}
defines these operations for any type \AgdaRef{A} with an equality
operation \AgdaRef{\_==\_\ :\ A\ →\ A\ →\ Bool}.

\begin{comment}
 When an ordinary Agda type \AgdaRef{A} has an equality operation
\AgdaRef{\_==\_\ :\ A\ →\ A\ →\ Bool}, environments
\AgdaRef{ρ\ :\ ⟪\ A\ →ˢ\ D\ ⟫} can be `updated' (i.e., extended or
overridden) using the conventional notation
\AgdaRef{ρ\ {[}\ δ\ /\ a\ {]}}, defined as follows. 
\end{comment}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
module Updates where
  open Flat
  open Flat.Booleans
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
  -- ρ [ δ / a ] maps a to δ, and other arguments a′ to ρ a′
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′
\end{code}
\end{AgdaSuppressSpace}
%
\begin{comment}
 Similarly for stores \AgdaRef{σ\ :\ ⟪\ (A\ +⊥)\ →ᶜ\ D\ ⟫}: 
\end{comment}
%
\begin{AgdaSuppressSpace}
\begin{code}[hide]
  open Flat
  _[_/_]⊥ : {{Eq A}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
  -- σ [ δ / α ]⊥ maps α to δ, and other arguments α′ to σ α′
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′
\end{code}
\end{AgdaSuppressSpace}
%
\begin{comment}
 Defining extension or overriding of \emph{dependent} maps is less
straightforward, as it involves a function that returns an
\emph{equivalence proof} instead of a truth value: 
\end{comment}
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
