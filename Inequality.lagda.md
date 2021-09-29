<!-- -*-agda2-*- -->

<!--
```
module Inequality where

open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Data.Bool renaming (Bool to 𝔹) hiding (_≤_)
open import Data.Nat hiding (_≤_ ; _≤ᵇ_)
import Data.Nat as ℕ
open import Data.Product using (_,_)

open import Function.Base using (_on_)
open import Data.Fin renaming (Fin to 𝔽) hiding (_≤_; _+_)
import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality

open import Categorical.Homomorphism hiding (true; false; refl; sym)
open import Functions
open import Categorical.Arrow Function renaming (mk to arr; _⇨_ to _⇛_) ; open _⇛_

```
-->

In this document we are going to try to derive an efficient implementation of
"less than or equal to" in hardware. We will start with the definition of `_≤ᵇ_`
on _natural numbers_. We use a slightly different, but equivalent, definition
to the definition of `_≤ᵇ_` in the Agda Standard Library. We have renamed it for
clarity.

```
ℕ² : Set
ℕ² = ℕ × ℕ

𝔽² : (i,j : ℕ²) → Set
𝔽² (i , j) = 𝔽 i × 𝔽 j
```

```
ℕ≤ : ℕ² → 𝔹
ℕ≤ (zero , _)      = true
ℕ≤ (suc m , zero)  = false
ℕ≤ (suc m , suc n) = ℕ≤ (m , n)
```

As it turns out there is no equivalent definition of a `_≤ᵇ_` operator in the
Standard Library's `Data.Fin` module. However, `_≤_` is defined as a
_type synonym_ as follows:


    _≤_ : ∀ {n} → Rel (Fin n) 0ℓ
    _≤_ = ℕ._≤_ on toℕ


The RHS simplifies to `λ x y → toℕ x ℕ.≤ toℕ y`

We choose to implement `_𝔽≤_` in a similar way. We directly define it as:


```
𝔽≤ : {i,j : ℕ²} → 𝔽² i,j → 𝔹
𝔽≤ (m , n) = ℕ≤ (toℕ m , toℕ n)
```

Let's start with a trivial proof. The type so closely follows the definition of `𝔽≤`
that we can just use `refl`.

```
toℕ² : {i,j : ℕ²} → 𝔽² i,j → ℕ²
toℕ² (m , n) = (toℕ m , toℕ n)
```

       ℕ²  --- ℕ≤ --- 𝔹
       |              |
      toℕ²            id
       |              |
      𝔽² k --- 𝔽≤ --- 𝔹

```
toℕ-≤ : {i,j : ℕ²} → 𝔽≤ {i,j} ≗ ℕ≤ ∘ toℕ²
toℕ-≤ _ = refl
```

Let's now encapsulate that proof using an instance of an _arrow category_.

```
𝔽≤⇉ : {i,j : ℕ²} → toℕ² {i,j} ⇉ id
𝔽≤⇉ = arr 𝔽≤ ℕ≤ toℕ-≤
```

For want of a better term we are going to call this a
Specification-Implementation-Mapping Proof (SIM proof) in the rest of
this note.

## A first attempt at defining inequality on multi-digit representations

Computing inequality for a unary representation is expensive. An
inspection of `ℕ≤` reveals that `min (m , n)` steps are required to
compute `m ℕ≤ n`. We can improve the performance by attempting to
derive an algorithm that works on a representation of numbers in a
_positional_ number system.

Consider two base 10 numbers, say, 34 and 123. Let's stack them on
top of each other, as follows.

    34
   123

Because 34 is only a 2-digit number and 123 is a 3-digit number
we can quickly deduce that 34 ≤ 123. This suggest that comparison
should go in order from the most significant digits down to the least
significant digits. If we think of 34 as the three-digit number 034.
We can see that the 0 from 034 is less than or equal to the 1 from 123
and thus we can stop with a result of `true`. The opposite is true if
the most significant digit of the first number is greater than the
second, and we yield the result `false`. If the most significant
digit is equal we must check the remaining digits.

It looks like we are going to need to define less-than and equality
operators for both `ℕ` and `𝔽`.

```
𝔽< : {i,j : ℕ²} → 𝔽² i,j → 𝔹
𝔽< (zero  , suc _) = true
𝔽< (_     , zero ) = false
𝔽< (suc m , suc n)= 𝔽< (m , n)

𝔽= : {i,j : ℕ²} → 𝔽² i,j → 𝔹
𝔽= (zero  , zero ) = true
𝔽= (zero  , suc _) = false
𝔽= (suc _ , zero ) = false
𝔽= (suc m , suc n) = 𝔽= (m , n)
```

Just like for the operation of addition, it looks like some notion of
_carry-in_ becomes necessary when doing inequality on multi-digit
numbers. The necessity of carry-in implies that carry-out is also
necessary so that it may be fed into the comparison of the next digit
position.

Using our previous discussion of the comparison of 34 and 123 as
inspiration, at first it seems like the carry-in should be a pair of
booleans, one denoting whether the two digits are less-than each
other and the other denoting whether they are equal.

However, we quickly see that when the boolean denoting less-than is
true this implies the boolean denoting equality is false, and vice
versa.

This leads us to consider a new data type.

## Generalising from less-than-or-equal to a comparison relation

Instead of a pair of booleans denoting less-than and equality
relationships between two numbers, we can instead ask "what is the
relationship between two numbers"? This leads us to define to the
following data type `R` which denotes whether two numbers are
less-than, equal, or greater-than each other respectively.


```
data R : Set where
  is< : R
  is= : R
  is> : R
```

This has some immediate implications. First, in order to define a
less-than-or-equal function which returns a boolean we will now
require an auxillary function of type `R → 𝔹`. Fortunately, this
is trivial to define.

```
R-is≤ : R → 𝔹
R-is≤ is< = 𝕥
R-is≤ is= = 𝕥
R-is≤ is> = 𝕗
```

Second, but much more importantly, we have shifted to solving a more
general problem which will yield immediate dividends. In the process
of deriving a less-than-or-equal function we have come up with a
building block that can be used for equality and any of the other
inequality relations. This delights me.

Now that we have declared the `R` data type we no longer have need of
functions `F<`, `F=`, etc. Instead we define a function `𝔽-compare`.

```
𝔽-compare : {i,j : ℕ²} → 𝔽² i,j → R
𝔽-compare (zero , zero)    = is=
𝔽-compare (zero , suc _)   = is<
𝔽-compare (suc _ , zero)   = is>
𝔽-compare (suc m , suc n)  = 𝔽-compare (m , n)
```


```
ℕ-compare : ℕ² → R
ℕ-compare (zero , zero)    = is=
ℕ-compare (zero , suc _)   = is<
ℕ-compare (suc _ , zero)   = is>
ℕ-compare (suc m , suc n)  = ℕ-compare (m , n)

toℕ²-ℕ-compare : {i,j : ℕ²} → 𝔽-compare {i,j} ≗ ℕ-compare ∘ toℕ²
toℕ²-ℕ-compare (zero  , zero)  = refl
toℕ²-ℕ-compare (zero  , suc _) = refl
toℕ²-ℕ-compare (suc _ , zero)  = refl
toℕ²-ℕ-compare (suc m , suc n) = toℕ²-ℕ-compare (m , n)
```

```
relation𝔽 : {i,j : ℕ²} → R × 𝔽² i,j → R
relation𝔽 (is< , _ , _) = is<
relation𝔽 (is= , m , n) = 𝔽-compare (m , n)
relation𝔽 (is> , m , n) = is>
```


      R × ℕ² --- relationℕ ---> R
        ^                       ^
        |                       |
     id ⊗ toℕ²                 id
        |                       |
     R × 𝔽² --- relation𝔽 ----> R

Just like for the operation of addition we will need to "guess" what
the definition of `relationℕ` should be, but we will quickly find out
whether it is correct or not when we try to prove the commutative
diagram holds.


```
relationℕ : R × ℕ² → R
relationℕ (is< , _ , _) = is<
relationℕ (is= , m , n) = ℕ-compare (m , n)
relationℕ (is> , m , n) = is>
```

The property we need to prove is called `toℕ²-relationℕ`.


```

eq-relation𝔽-relation𝔽 : {i,j : ℕ²} → (r : R) → (m,n :  𝔽² i,j) → relation𝔽 {i,j} (r , m,n) ≡ relationℕ (r , toℕ² m,n)
eq-relation𝔽-relation𝔽 is< m,n = refl
eq-relation𝔽-relation𝔽 is= m,n rewrite sym (toℕ²-ℕ-compare m,n) = refl
eq-relation𝔽-relation𝔽 is> m,n = refl

toℕ²-relationℕ : {i,j : ℕ²} → relation𝔽 {i,j} ≗ relationℕ ∘ (id ⊗ toℕ²)
toℕ²-relationℕ {i,j} (r , (m , n)) rewrite eq-relation𝔽-relation𝔽 {i,j} r (m , n) = refl
```

We can now package this up as a SIM proof.

```
relation𝔽⇉ : {i,j : ℕ²} → id ⊗ toℕ² {i,j} ⇉ id
relation𝔽⇉ = arr relation𝔽 relationℕ toℕ²-relationℕ
```
