# PCF Tests

The following tests check that the denotations of some expressions
in the abstract syntax of the PCF language compute the expected values
when applied to an arbitrary environment `ρ`.

All the `refl` proofs of the tests below implicitly use the rewrite rule postulated as
a [property of the fixed-point operator], 
together with the rule for [eliminating injections] in arguments of
extensions of functions to flat domains.

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Tests.PCF where
  open import Notation.Domains
  open import Properties.Functions
  open import Properties.Flat
  open import Examples.PCF.Abstract-Syntax
  open import Examples.PCF.Domain-Equations
  open import Examples.PCF.Semantic-Functions

  -- Typed variables:

  a  = α 0 ι
  b  = α 1 ι
  e  = α 2 ι
  
  g  = α 0 (ι ⇒ ι)
  h  = α 0 (ι ⇒ ι ⇒ ι)

  check-41+1 :
    𝒜′⟦ ⦅ 𝐿 ⦅+1⦆ ␣ 𝐿 k 41 ⦆ ⟧ ρ ≡ ↑ 42
  check-41+1 = refl

  check-43-1 :
    𝒜′⟦ ⦅ 𝐿 ⦅−1⦆ ␣ 𝐿 k 43 ⦆ ⟧ ρ ≡ ↑ 42
  check-43-1 = refl

  check-id :
    𝒜′⟦ ⦅ ⦅λ a ␣ 𝑉 a ⦆ ␣ 𝐿 k 42 ⦆ ⟧ ρ ≡ ↑ 42
  check-id = refl

  check-k :
    𝒜′⟦ ⦅ ⦅ ⦅λ a ␣ ⦅λ b ␣ 𝑉 a ⦆ ⦆ ␣ 𝐿 k 42 ⦆ ␣ 𝐿 k 41 ⦆ ⟧ ρ ≡ ↑ 42
  check-k = refl

  check-ki :
    𝒜′⟦ ⦅ ⦅ ⦅λ a ␣ ⦅λ b ␣ 𝑉 b ⦆ ⦆ ␣ 𝐿 k 41 ⦆ ␣ 𝐿 k 42 ⦆ ⟧ ρ ≡ ↑ 42
  check-ki = refl

  check-suc-41 :
    𝒜′⟦ ⦅ ⦅λ a ␣ ⦅ 𝐿 ⦅+1⦆ ␣ 𝑉 a ⦆ ⦆ ␣ 𝐿 k 41 ⦆ ⟧ ρ ≡ ↑ 42
  check-suc-41 = refl

  check-pred-42 :
    𝒜′⟦ ⦅ ⦅λ a ␣ ⦅ 𝐿 ⦅−1⦆ ␣ 𝑉 a ⦆ ⦆ ␣ 𝐿 k 43 ⦆ ⟧ ρ ≡ ↑ 42
  check-pred-42 = refl

  check-if-zero :
    𝒜′⟦ ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝐿 k 0 ⦆ ⦆ ␣ 𝐿 k 42 ⦆ ␣ 𝐿 k 0 ⦆ ⟧ ρ ≡ ↑ 42
  check-if-zero = refl

  check-if-nonzero :
    𝒜′⟦ ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝐿 k 42 ⦆ ⦆ ␣ 𝐿 k 0 ⦆ ␣ 𝐿 k 42 ⦆ ⟧ ρ ≡ ↑ 42
  check-if-nonzero = refl

  check-fix-const :
    𝒜′⟦ ⦅ 𝐿 Y ␣ ⦅λ e ␣ 𝐿 k 42 ⦆ ⦆ ⟧ ρ ≡ ↑ 42
  check-fix-const = refl

  check-fix-lambda : -- fix (λg. λa. 42) 2 ≡ 42
    𝒜′⟦ ⦅ ⦅ 𝐿 Y ␣ ⦅λ g ␣ ⦅λ a ␣ 𝐿 k 42 ⦆ ⦆ ⦆ ␣ 𝐿 k 2 ⦆ ⟧ ρ ≡ ↑ 42
  check-fix-lambda = refl

  check-countdown : -- fix (λg. λa. ifz a then 42 else g (pred a)) 5 ≡ 42
    𝒜′⟦ ⦅ ⦅ 𝐿 Y ␣ ⦅λ g ␣ ⦅λ a ␣
                ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝑉 a ⦆ ⦆ ␣ 𝐿 k 42 ⦆ ␣
                      ⦅ 𝑉 g ␣ ⦅ 𝐿 ⦅−1⦆ ␣ 𝑉 a ⦆ ⦆ ⦆ ⦆ ⦆ ⦆ ␣ 𝐿 k 5 ⦆ ⟧ ρ ≡ ↑ 42
  check-countdown = refl

  check-sum-42 : -- fix (λh.λa.λb. ifz a then b else h(pred a)(𝐿 ⦅+1⦆ b)) 4 38 ≡ 42
    𝒜′⟦ ⦅ ⦅ ⦅ 𝐿 Y ␣ ⦅λ h ␣ ⦅λ a ␣ ⦅λ b ␣
                    ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝑉 a ⦆ ⦆ ␣ 𝑉 b ⦆ ␣ 
                      ⦅ ⦅ 𝑉 h ␣ ⦅ 𝐿 ⦅−1⦆ ␣ 𝑉 a ⦆ ⦆ ␣ ⦅ 𝐿 ⦅+1⦆ ␣ 𝑉 b ⦆ ⦆ ⦆ ⦆ ⦆ ⦆ ⦆
        ␣ 𝐿 k 4 ⦆ ␣ 𝐿 k 38 ⦆ ⟧ ρ ≡ ↑ 42
  check-sum-42 = refl
```

[property of the fixed-point operator]: ../Properties/Functions.md#function-domains
[eliminating injections]: ../Properties/Flat/index.md#flat-domains
