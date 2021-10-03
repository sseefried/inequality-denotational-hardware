<!-- -*-agda2-*- -->

<!--
```
module Inequality where

open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Data.Bool renaming (Bool to 𝔹) hiding (_≤_;not;_∧_)
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

𝔹² : Set
𝔹² = 𝔹 × 𝔹
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

We also define an equivalent function on ℕ and prove a correspondence
between the two.

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

We are now finally in a position to define a comparison function
involving carry-in/out. We use the a super-script `c` (`ᶜ`) in the
name to distinguish it.

We are immediately faced with the question: what should the type of
this function be? The source type is easy. It should be the carry-in
along with the two numbers to compare. Note, here we set the numbers
to have the same bound `k` since we are looking at the specific case
of comparing two numbers that use the same positional number system
including the base of each digit.

```
Cⁱ : Set → Set
Cⁱ a = R × a

𝔽Cⁱ : ℕ → Set
𝔽Cⁱ k = Cⁱ (𝔽² (k , k))

ℕCⁱ : Set
ℕCⁱ = Cⁱ ℕ²
```

But what about the target type? For the case of addition it was a pair
containing the result of the adding the two numbers along with the
carry-out bit. However, in the case of less-than-or-equal, our result
type _is the same as_ our carry-in type. Thus we just return a value
of type `R`.  Later, when we use our function to compare multiple
digits we just feed the result in _as_ the carry-in to the next
invocation.

Here is the definition of `𝔽-compareᶜ`.

```
𝔽-compareᶜ : {k : ℕ} → 𝔽Cⁱ k → R
𝔽-compareᶜ (is< , _ , _) = is<
𝔽-compareᶜ (is= , m , n) = 𝔽-compare (m , n)
𝔽-compareᶜ (is> , m , n) = is>
```

What does comparison-with-carry look like on natural numbers? It
should satisfy the following commutative diagram.


       ℕCⁱ --- ℕ-compareᶜ ---> R
        ^                      ^
        |                      |
     id ⊗ toℕ²                 id
        |                      |
      𝔽Cⁱ k - 𝔽-compareᶜ ----> R

Just like for the operation of addition we will need to "guess" what
the definition of `ℕ-compareᶜ` should be, but we will quickly find out
whether it is correct or not when we try to prove the commutative
diagram holds.


```
ℕ-compareᶜ : ℕCⁱ → R
ℕ-compareᶜ (is< , _ , _) = is<
ℕ-compareᶜ (is= , m , n) = ℕ-compare (m , n)
ℕ-compareᶜ (is> , m , n) = is>
```

The property we need to prove is called `toℕ²-ℕ-compareᶜ`.

```
-- Helper proof
eq-𝔽-compareᶜ-𝔽-compareᶜ : {k : ℕ} → (r : R) → (m,n :  𝔽² (k , k)) → 𝔽-compareᶜ {k} (r , m,n) ≡ ℕ-compareᶜ (r , toℕ² m,n)
eq-𝔽-compareᶜ-𝔽-compareᶜ is< m,n = refl
eq-𝔽-compareᶜ-𝔽-compareᶜ is= m,n rewrite sym (toℕ²-ℕ-compare m,n) = refl
eq-𝔽-compareᶜ-𝔽-compareᶜ is> m,n = refl

toℕ²-ℕ-compareᶜ : {k : ℕ} → 𝔽-compareᶜ {k} ≗ ℕ-compareᶜ ∘ (id ⊗ toℕ²)
toℕ²-ℕ-compareᶜ {k} (r , (m , n)) rewrite eq-𝔽-compareᶜ-𝔽-compareᶜ {k} r (m , n) = refl
```

We can now package this up as a SIM proof.

```
𝔽-compareᶜ⇉ : {k : ℕ} → id ⊗ toℕ² {k , k} ⇉ id
𝔽-compareᶜ⇉ = arr 𝔽-compareᶜ ℕ-compareᶜ toℕ²-ℕ-compareᶜ
```

## Abstracting on comparison functions

At this point we could be hasty and simply derive a comparison
function that uses bit vectors. But let's _not_ be hasty. To avoid this
we can abstract over the notion of comparison-with-carry.

Using a similar idea from Conal's "Adders and Arrows" note, we replace
the representation type, `𝔽 k`, with an arbitrary representation type `τ`
and introduce a meaning function `μ : τ → 𝔽 k` for some `k : ℕ`.

```
τCⁱ : Set → Set
τCⁱ τ =  R × τ × τ
```

It should satisfy the following commutative diagram:

      𝔽Cⁱ k -- 𝔽-compareᶜ --> R
        ^                    ^
        |                    |
    id ⊗ μ ⊗ μ               id
        |                    |
      τCⁱ k --- compareᶜ ---> R

In code:

```
is-compare : { τ : Set } {k : ℕ} (μ : τ → 𝔽 k) (compareᶜ : τCⁱ τ → R) → Set
is-compare μ compareᶜ = compareᶜ ≗ 𝔽-compareᶜ ∘ (id ⊗ μ ⊗ μ)
```

Let's now package `compareᶜ` functions along with proofs that they are valid
refinements of `𝔽-compareᶜ`.

```
infix 1 _⊣_
record Comparison {τ : Set} {k : ℕ} (μ : τ → 𝔽 k) : Set where
  constructor _⊣_
  field
    compareᶜ : τCⁱ τ → R
    is : is-compare μ compareᶜ
```

We can now define a SIM proof _generator_ that, given a value of type `Comparison μ`
yields a SIM proof satisfying the commutative diagram above.

```
mk-compareᶜ⇉ : {τ : Set} {k : ℕ} {μ : τ → 𝔽 k} → Comparison μ → id ⊗ μ ⊗ μ ⇉ id
mk-compareᶜ⇉ (compareᶜ ⊣ is) = arr compareᶜ 𝔽-compareᶜ is
```

A SIM proof generator for the entire commutative tower is given below.

```
mk-tower⇉ : {τ : Set} {k : ℕ} {μ : τ → 𝔽 k} →
  Comparison μ → (id ⊗ toℕ²) ∘ (id ⊗ μ ⊗ μ) ⇉ id
mk-tower⇉ comparison = 𝔽-compareᶜ⇉ ◎ mk-compareᶜ⇉ comparison
```

## A single-bit comparison function

We can now look at implementing a single bit inequality
function. However, if we are going to generate a circuit from this we
will have to use boolean values to represent values of both type `R`
and `𝔽 2`.

For values of type `R` we produce a pair where the first component
represents whether the value is `is<` and the second whether the value
is `is=`.

```
R-to-𝔹² : R → 𝔹²
R-to-𝔹² is< = (𝕥 , 𝕗)
R-to-𝔹² is= = (𝕗 , 𝕥)
R-to-𝔹² is> = (𝕗 , 𝕗)
```

There are 4 values that can be represented by a pair of booleans, so
one will necessarily not appear on the right hand side of this
definition. Using the representation we have chosen it is cleary `(𝕥 ,
𝕥)`. Fortunately, this value would be meaningless since two numbers
cannot both be less-than and equal to each other. Nevertheless, the
redundancy of the `B²` type in representing `R` values does not sit
well with me, and seems inelegant. Perhaps this could be improved.

We want `R-to-𝔹²` to be invertible but this leads us to the question
of what we should do with the input `(𝕥 , 𝕥)`. One choice is that it
represents `is<` if we slightly modify the meaning of the pair of
booleans to mean that the second component only has a meaning if the
first component is `𝕗`. This leads to this definition:


    𝔹²-to-R :  𝔹² → R
    𝔹²-to-R (𝕥 , _) = is<
    𝔹²-to-R (𝕗 , 𝕥) = is=
    𝔹²-to-R (𝕗 , 𝕗) = is>


Unfortunately this means that the function is not invertible in one direction, since the
following is true.

    (R-to-𝔹² ∘ 𝔹²-to-R) (𝕥 , 𝕥) = (𝕥 , 𝕗)

Thus we cannot prove that `R-to-𝔹² ∘ 𝔹²-to-R ≗ id`

I suspect this is going to bite us, and pretty soon, but since I don't
know how to solve this problem we will press on.


Next we define `F𝟚-to-𝔹` and `𝔹-to­𝔽2` as follows:
```
F𝟚-to-𝔹 : 𝔽 2 → 𝔹
F𝟚-to-𝔹 zero       = 𝕗
F𝟚-to-𝔹 (suc zero) = 𝕥

𝔹-to-𝔽2 : 𝔹 → 𝔽 2
𝔹-to-𝔽2 𝕗 = zero
𝔹-to-𝔽2 𝕥 = suc zero
```

We can now sketch the commutative diagram that must be satisfied:


        R × 𝔽² (2 , 2) --- 𝔽-compareᶜ ---> R
              ^                            ^
              |                            |
       𝔹²-to-R ⊗ 𝔹-to-𝔽2 ⊗ 𝔹-to-𝔽2     𝔹²-to-R
              |                            |
           𝔹² × B² ------- compareᶜ ------> 𝔹²
