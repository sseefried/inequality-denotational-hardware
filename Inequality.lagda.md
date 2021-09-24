<!-- -*-agda2-*- -->

<!--
```
module Inequality where

open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Data.Bool renaming (Bool to 𝔹) hiding (_≤_)
open import Data.Nat hiding (_≤_ ; _≤ᵇ_)
import Data.Nat as ℕ
open import Function.Base using (_on_)
open import Data.Fin renaming (Fin to 𝔽) hiding (_≤_)
import Data.Nat.Properties
```
-->

In this document we are going to try to derive an efficient implementation of
"less than or equal to" in hardware. We will start with the definition of `_≤ᵇ_`
on _natural numbers_. We use a slightly different, but equivalent, definition
to the definition of `_≤ᵇ_` in the Agda Standard Library. We have renamed it for
clarity.

```
_ℕ≤_ : ℕ → ℕ → 𝔹
zero ℕ≤ _      = true
suc m ℕ≤ zero  = false
suc m ℕ≤ suc n = m ℕ≤ n
```

As it turns out there is no equivalent definition of a `_≤ᵇ_` operator in the
Standard Library's `Data.Fin` module. However, `_≤_` is defined as a
_type synonym_ as follows:


    _≤_ : ∀ {n} → Rel (Fin n) 0ℓ
    _≤_ = ℕ._≤_ on toℕ


The RHS simplifies to `λ x y → toℕ x ℕ.≤ toℕ y`

We choose to do implement `_𝔽≤_` in a similar way. We directly define it as:


```
_𝔽≤_ : {m : ℕ} → 𝔽 m → 𝔽 m → 𝔹
m 𝔽≤ n = toℕ m ℕ≤ toℕ n
```
