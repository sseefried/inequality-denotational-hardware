<!-- -*-agda2-*- -->

<!--
```
{-# OPTIONS --guardedness #-}  -- For tesing/IO
module Inequality where

open import Relation.Binary.Core using (Rel)
open import Data.Bool renaming (Bool to 𝔹) hiding (_≤_;not;_∧_; true; false)
open import Data.Bool.Properties
open import Data.Nat hiding (_≤_ ; _≤ᵇ_;_≟_; compare)
import Data.Nat as ℕ
open import Data.Unit using (tt)
open import Data.Empty
open import Data.Product using (_,_)
open import Data.Fin renaming (Fin to 𝔽) hiding (_≤_; _+_;_≟_;compare)
import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Categorical.Raw using (xor)
open import Categorical.Homomorphism hiding (refl; sym)
open import Functions
open import Categorical.Arrow Function renaming (mk to arr; _⇨_ to _⇛_) ; open _⇛_
open import Relation.Nullary
open import Relation.Nullary.Decidable
```
-->

In this document we derive efficient comparison circuits. The original
goal was to derive an efficient implementation of the
less-than-or-equal-to comparison circuit, but it became quickly
apparent that solving a more general problem was the right thing to
do.

The design philosophy followed in this document is quite different to
the common approach. Rather than attempt a proof of correctness only
after the implementation is complete, design and proof of correctness
are performed simultaneously. In fact correctness proofs are often
kept deliberately abstract, in the sense that they prove correctness
over a family of implementations. These proofs often have parameters
that can be provided to produce a more concrete proof of correctness.

Throughout this process we strive to keep the mathematical
specification and the implementation as distinct concepts. In
particular we do not allow operational concerns to influence the top
level mathematical specification.

However, the design process is performed in a stepwise manner. At each
step we can introduce operational concerns, such as bounds on numbers,
but the point is not to do this too early in the process as it is
unnecessarily restrictive and can prevent one from seeing elegant and
powerful implementations.

To illustrate this point consider the list (`[]`) data type in
Haskell.  To the Haskell beginner, consuming output from a function
that produces an infinite list seems like it must yield a program
which does not terminate. However, Haskell's non-strict semantics have
the delightful consequence that they make this untrue.  Had the
designers of Haskell unnecessarily restricted their thought with the
operational concern that all computers have finite memory it's
possible that they would never have seen the possibility of finitely
consuming the results of a function which produced an infinite list.

As an organising principle for this document I will try to, as much as
possible, reflect the entire design process, including work that was
thrown away but nevertheless provided insight for more promising
avenues that eventually led to the final result.

To start, we will look at specifying just the less-than-or-equal-to
operator and see where that takes us.

## Starting with less-than-or-equal-to


We first define some notational conveniences. `𝔽` and `𝔹` are just
shorthand for finite sets and booleans respectively. The "squared"
versions of these types (and natural numbers) allow us to succinctly
denote products of these types.

```
ℕ² : Set
ℕ² = ℕ × ℕ

𝔽² : (i,j : ℕ²) → Set
𝔽² (i , j) = 𝔽 i × 𝔽 j

𝔹² : Set
𝔹² = 𝔹 × 𝔹
```

As our specification of the less-than-or-equal-to operator we use a
slightly different, but equivalent, definition to the definition of
`_≤ᵇ_` in the Agda Standard Library. We have renamed it for clarity.


```
ℕ≤ : ℕ² → 𝔹
ℕ≤ (zero , _)      = 𝕥
ℕ≤ (suc m , zero)  = 𝕗
ℕ≤ (suc m , suc n) = ℕ≤ (m , n)
```

We now come to the first refinement in the design process. The unary
representation of natural numbers, while easy to reason about, is a
very inefficient representation. An inspection of `ℕ≤` reveals that
`min (m , n)` steps are required to compute `ℕ≤ (m, n)`. Thus we we'll
want to investigate a multi-digit representation of numbers.  Digits
themselves are bounded by the base they represent. For instance, there
are ten decimal digits and two binary digits. Thus we'll want to
define a comparison function on finite sets.

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

We now define a commutative diagram to represent the properties we
want this refinement to have.

       ℕ²  --- ℕ≤ ---> 𝔹
       ^               ^
       |               |
      toℕ²            id
       |               |
      𝔽² k --- 𝔽≤ ---> 𝔹


Function `toℕ²` is defined as:

```
toℕ² : {i,j : ℕ²} → 𝔽² i,j → ℕ²
toℕ² (m , n) = (toℕ m , toℕ n)
```

Let's start with a trivial proof of the commutativity of the
diagram. The type of `toℕ²` so closely follows the body of `𝔽≤` that
we can just use `refl`.

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

## A first attempt at defining ≤ on multi-digit representations

As I mentioned before computing ≤ for a unary representation is
expensive. An inspection of `ℕ≤` reveals that `min (m , n)` steps are
required to compute `ℕ≤ (m, n)`. We can improve the performance by
attempting to derive an algorithm that works on a representation of
numbers in a _positional_ number system.

Consider two base 10 numbers, say, 34 and 123. Let's stack them on
top of each other, as follows.

    34
   123

Because 34 is only a 2-digit number and 123 is a 3-digit number
we can quickly deduce that 34 ≤ 123.

This suggests that comparison should go in order from the most
significant digits down to the least significant digits. If we think
of 34 as the three-digit number 034.  We can see that the 0 from 034
is less than or equal to the 1 from 123 and thus we can stop with a
result of `true`. The opposite is true if the most significant digit
of the first number is greater than the second, and we yield the
result `false`. If the most significant digit is equal we must check
the remaining digits.

As it turns out, this was incorrect, but I'll wait until later to
reveal why. For now, we'll continue in this direction.

It looks like we are going to need to define less-than and equality
operators for both `ℕ` and `𝔽`.

```
𝔽< : {i,j : ℕ²} → 𝔽² i,j → 𝔹
𝔽< (zero  , suc _) = 𝕥
𝔽< (_     , zero ) = 𝕗
𝔽< (suc m , suc n)= 𝔽< (m , n)

𝔽= : {i,j : ℕ²} → 𝔽² i,j → 𝔹
𝔽= (zero  , zero ) = 𝕥
𝔽= (zero  , suc _) = 𝕗
𝔽= (suc _ , zero ) = 𝕗
𝔽= (suc m , suc n) = 𝔽= (m , n)
```

At this point I made my second design mistake. It seemed like some notion of
_carry-in_ was necessary when doing less-than-or-equal-to on multi-digit
numbers.

I reasoned that the necessity of carry-in implies that carry-out was also
necessary so that it may be fed into the comparison of the next digit
position.

Using our previous discussion of the comparison of 34 and 123 as
inspiration, at first it then seemed reasonable that the carry-in
should be a pair of booleans, one denoting whether the two digits are
less-than each other and the other denoting whether they are equal.

However, this led to an insight. We quickly see that when the boolean
denoting less-than is true this implies the boolean denoting equality
is false, and vice versa.

This led me to consider a new data type.

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
functions `𝔽<`, `𝔽=`, etc. Instead we define a function `𝔽-compare`.

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
```

        ℕ² --- ℕ-compare ----> R
        ^                      ^
        |                      |
       toℕ²                    id
        |                      |
       𝔽 i,j --- 𝔽-compare --> R

```
toℕ²-ℕ-compare : {i,j : ℕ²} → 𝔽-compare {i,j} ≗ ℕ-compare ∘ toℕ²
toℕ²-ℕ-compare (zero  , zero)  = refl
toℕ²-ℕ-compare (zero  , suc _) = refl
toℕ²-ℕ-compare (suc _ , zero)  = refl
toℕ²-ℕ-compare (suc m , suc n) = toℕ²-ℕ-compare (m , n)
```

We package this up as a SIM Proof as follows:

```
𝔽-compare⇉ : {i,j : ℕ²} → toℕ² {i,j} ⇉ id
𝔽-compare⇉  = arr 𝔽-compare ℕ-compare toℕ²-ℕ-compare
```

## A one-bit comparison function

Before going on we'll perform another refinement down to a single
digit binary comparison function.
[TODO: explain central techniques like the commutative tower]

However, if we are going to generate a circuit from this we
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
well with me, and seems inelegant. The non-redundant representation of
sum types like `R` is still an open problem in want of a solution.

We want `R-to-𝔹²` to be invertible but this leads us to the question
of what we should do with the input `(𝕥 , 𝕥)`. One choice is that it
represents `is<` if we slightly modify the meaning of the pair of
booleans to mean that the second component only has a meaning if the
first component is `𝕗`. This leads to this definition:


```
𝔹²-to-R :  𝔹² → R
𝔹²-to-R (𝕥 , _) = is<
𝔹²-to-R (𝕗 , 𝕥) = is=
𝔹²-to-R (𝕗 , 𝕗) = is>
```

Unfortunately this means that the function is not invertible in one direction, since the
following is true.

    (R-to-𝔹² ∘ 𝔹²-to-R) (𝕥 , 𝕥) = (𝕥 , 𝕗)

Thus we cannot prove that `R-to-𝔹² ∘ 𝔹²-to-R ≗ id` but we can prove
`𝔹²-to-R ∘ R-to-𝔹² ≗ id`.



Next we define a pair of functions `F𝟚-to-𝔹` and `𝔹-to­𝔽2` for
converting between finite sets of cardinality two and booleans and
vice versa.

```
F𝟚-to-𝔹 : 𝔽 2 → 𝔹
F𝟚-to-𝔹 zero       = 𝕗
F𝟚-to-𝔹 (suc zero) = 𝕥

𝔹-to-𝔽2 : 𝔹 → 𝔽 2
𝔹-to-𝔽2 𝕗 = zero
𝔹-to-𝔽2 𝕥 = suc zero
```



Our commutative tower now looks like this

        ℕ² --- ℕ-compare -----> R
        ^                       ^
        |                       |
       toℕ²                     id
        |                       |
       𝔽 2,2 --- 𝔽-compare ---> R
        ^                       ^
        |                       |
   𝔹-to-𝔽2 ⊗ 𝔹-to-𝔽2         𝔹²-to-R
        |                       |
        𝔹² --- 𝔹-compare-𝔹² --> 𝔹²


Now all that remains is to define `𝔹-compare-𝔹²`.

We do a simple case analysis on `𝔽-compare` along with the following,
machine-checked, facts to yield a preliminary definition for
`𝔹-compare-𝔹²`.

```
𝕗-is-zero : 𝔹-to-𝔽2 𝕗 ≡ zero
𝕗-is-zero = refl

𝕥-is-one : 𝔹-to-𝔽2 𝕥 ≡ suc zero
𝕥-is-one = refl

𝔹-compare-𝔹²₀ : 𝔹² → 𝔹²
𝔹-compare-𝔹²₀ (𝕗 , 𝕗) = R-to-𝔹² is=
𝔹-compare-𝔹²₀ (𝕗 , 𝕥) = R-to-𝔹² is<
𝔹-compare-𝔹²₀ (𝕥 , 𝕗) = R-to-𝔹² is>
𝔹-compare-𝔹²₀ (𝕥 , 𝕥) = 𝔹-compare-𝔹²₀ (𝕗 , 𝕗)
```

Simplifying, this yields

```
𝔹-compare-𝔹²₁ : 𝔹² → 𝔹²
𝔹-compare-𝔹²₁ (𝕗 , 𝕗) = (𝕗 , 𝕥)
𝔹-compare-𝔹²₁ (𝕗 , 𝕥) = (𝕥 , 𝕗)
𝔹-compare-𝔹²₁ (𝕥 , 𝕗) = (𝕗 , 𝕗)
𝔹-compare-𝔹²₁ (𝕥 , 𝕥) = (𝕗 , 𝕥)
```

This can be simplified to use the "fork" operator `▵`.

```
𝔹-compare-𝔹²₂ : 𝔹² → 𝔹²
𝔹-compare-𝔹²₂ = comp-fst ▵ comp-snd
  where
    comp-fst : 𝔹² → 𝔹
    comp-fst (𝕗 , 𝕗) = 𝕗
    comp-fst (𝕗 , 𝕥) = 𝕥
    comp-fst (𝕥 , 𝕗) = 𝕗
    comp-fst (𝕥 , 𝕥) = 𝕗

    comp-snd : 𝔹² → 𝔹
    comp-snd (𝕗 , 𝕗) = 𝕥
    comp-snd (𝕗 , 𝕥) = 𝕗
    comp-snd (𝕥 , 𝕗) = 𝕗
    comp-snd (𝕥 , 𝕥) = 𝕥
```

We now use our knowledge of boolean function primitives and the "truth table" evident
in the definition above to yield:

[TODO: make this more explicit]

```
𝔹-compare-𝔹² : 𝔹² → 𝔹²
𝔹-compare-𝔹² = (∧ ∘ first not) ▵ (not ∘ xor)
```

## 3-bit representation of `R`

It seems common in traditional hardware design to use a "one-hot"
3-bit representation of the `R` type. That is, three wires only one of
which can be true, the rest being false.

```
𝔹³ : Set
𝔹³ = 𝔹 × 𝔹 × 𝔹
```

Defining `R-to-𝔹³` is straightforward.

```
R-to-𝔹³ : R → 𝔹³
R-to-𝔹³ is< = (𝕥 , 𝕗 , 𝕗)
R-to-𝔹³ is= = (𝕗 , 𝕥 , 𝕗)
R-to-𝔹³ is> = (𝕗 , 𝕗 , 𝕥)
```

However, the inverse function is even trickier to define than
`𝔹²-to-R`. We want a total function but there is a even more
redundancy in the representation then for the 2-bit case since 3 bits
can represent 8 different values. We must have cases for when there is
more than "one hot wire" and we must also consider the case where none
of them are "hot".

We choose `is<` as our "no hot" case and use a priority-based encoding
for the other cases.  Each of the positions in the triple denote
`is<`, `is=` and `is>` respectively, but this is also the order of
priority.

If a `𝕥` appears in the `is<` position then it overrides whatever is
in the other two positions.  The `is=` is similar. It has priority
over the `is>` value but only when a `𝕗` appears in the `is<`
position. This leads us to the following definition:


```

𝔹³-to-R : 𝔹³ → R
𝔹³-to-R (𝕗 , 𝕗 , 𝕗) = is<
𝔹³-to-R (𝕥 , _ , _) = is<
𝔹³-to-R (𝕗 , 𝕥 , _) = is=
𝔹³-to-R (𝕗 , 𝕗 , 𝕥) = is>
```

We are now in a position to define `𝔹-compare-𝔹³`.

[TODO: Consider not defining this at all at this point and wait
for the later approach]

```
𝔹-compare-𝔹³ : 𝔹² → 𝔹³
𝔹-compare-𝔹³ = (∧ ∘ first not) ▵ (not ∘ xor) ▵ (∧ ∘ second not)
```

## Why the multi-digit comparison with carry approach is undesirable

I mentioned earlier that I tried an approach where the comparison
function for each digit was given a carry in. This proved to be
undesirable and in this section I will show you why.

I was unduly influenced by the ripple adder circuit and also the
"obvious" observation that one would want, when comparing to
multi-digit numbers, to examine them in order from most significant
digit to least.

Following this line of thought, when comparing digit by digit, we
would require the result of the comparison on the previous digit to be
carried in to the comparison on the current digit. A moment's thought
leads to this type signature:

    𝔽-compareᶜ : {i,j : ℕ} → R × 𝔽² i,j → R

Even at this point I was uneasy since the carry-in value was of type
`R`, which is also the result type. This is quite different to the
case for ripple adders where there is a distinction between the result
of adding two digits and the carry-out value of adding those two
digits. That is, an adder for a digit produces a pair of results.

Also something quite odd happens when one considers the case where the
carry-in value is `is<` or `is>`.

    𝔽-compareᶜ (is< , _ , _) = is<
    𝔽-compareᶜ (is> , _ , _) = is>

I took the refinement process through to its logical conclusion, and
it led to an implementation in hardware that sequentially composed
circuits that simply passed through the previous result. However this
came at the cost of extra circuitry that increased the _depth_ of the
circuit, using the definition that _depth_ of a circuit is the longest
sequence of gates connected by wires.

In the next section we will see an alternative approach which
eventually yields circuits with more gates (i.e. they perform more
_work_) but have less _depth_.

## The trade-off between work and depth in hardware and its relationship with semigroup folds.

CPUs, despite having multiple cores, still present a sequential
interface to the programmer. However, in the domain of hardware,
designing for parallism is the more natural paradigm.

One can often take a circuit with a lot of sequential composition and
change its design to an equivalent circuit with more gates but less
_depth_. An interesting question is: what high level design technique
leads naturally to more parallelism in circuits once the refinement
process has been carried out to its conclusion?

Surprisingly, at least to me, the answer to this question involves the
mathematical structure known as the semigroup. A semigroup consists of
a set of values of type, say, `τ` which are closed over an
_associative binary operator_ with signature `⊕ : τ → τ → τ`. It turns
out that the _associativity_ of the operator is the at heart of the
technique.

Consider the following combination of values:

    a ⊕ b ⊕ c ⊕ d

The associativity of the `⊕` ensures that the following expressions
all yield the same result: `(((a ⊕ b) ⊕ c) ⊕ d)`, `(a ⊕ (b ⊕ (c ⊕
d)))` and `((a ⊕ b) ⊕ (c ⊕ d))`. Which of these is the most efficient?
Which of these has the most parallelism. This is not something that
can be answered without a _cost model_ and a simple _operational
semantics_.

We will assume that any sub-expression can be evaluated if it is of
the form `x ⊕ y`. Each one of these will "cost" one "step". Also,
multiple such sub-expressions can be evaluated in parallel as long as
they do not contain further sub-expressions.

Using this simple operational semantics and cost model we can see that
`(a ⊕ (b ⊕ (c ⊕ d)))` takes 3 steps to evaluate and that it each
step only one sub-expression is evaluated. This is made explicit
below.


      a ⊕ (b ⊕ (c ⊕ d))
    ≡ a ⊕ (b ⊕ e)     where e = c ⊕ d
    ≡ a ⊕ f           where f = b ⊕ e
    ≡ g               where g = a ⊕ f


The evaluation of `(((a ⊕ b) ⊕ c) ⊕ d)` is similar except that
evaluation order is slightly different. However, evaluating `((a ⊕ b)
⊕ (c ⊕ d))` is a different story.

      (a ⊕ b) ⊕ (c ⊕ d)
    ≡ e ⊕ f     where e = a ⊕ b and f = c ⊕ d
    ≡ g               where g = e ⊕ f

This takes only 2 steps to evaluate because, in the first step `a
⊕ b` and `c ⊕ d` can be evaluated in parallel.

All of these expressions are _folds_ over values using the `⊕`
operator. In general, a fold over `2ⁿ` values (for some `n`) can be
performed in `log n` steps using the evaluation strategy above.

The operational semantics and cost model presented above can be
refined down to the level of circuits.  Parallel evaluations
correspond to computations performed by gates at the same depth in the
circuit, and the depth of the circuit corresponds to the number of
steps in the evaluation.

In the next section we investigate whether the `R` data type is a
semigroup. We discover that is a slighlty embelished structure known
as a _monoid_. A monoid, in addition to being closed over an associate
binary operator has a distinguished value, `e`, called the _identity_ such that
for all `a` both `a ⊕ e = a` and `e ⊕ a = a`.

## A monoid on `R`

Can we find an associative binary operator on `R`? Yes, it turns
out. We can do it by investigating what happens when we pair two
comparisons together.

Say we have compared `a` and `c` and also `b` and `d` and got a
result.  What should we say is the result of compareing `(a, b)` and
(c, d)`.  For inspiration we consider multi-digit representations of
numbers.  `13 < 23` precisely because `1 < 2`. But why is `13 <
14`?  The first digit is equal. Thus we must consult the second digit
for the final result. Another source of inspiration would be to
consider lexicographic ordering of strings.

This leads to the following definition of the operator, which we have
called `▲`.

```
▲ : R × R → R
▲ (is= , r₂) = r₂
▲ (is< , _)  = is<
▲ (is> , _)  = is>
```

By considering every pair of possible inputs (for a total of 9 cases)
one can convince oneself that this operator is associative and that
`is=` is the identity element. However, we can gain even more
assurance by proving this in Agda.

To do this we use the Standard Library's `Algebra` modules. This
requires we uncurry the `▲` operator as their definitions are only
defined in terms of uncurried functions.

```
open import Algebra.Core
open import Algebra.Structures {A = R} (_≡_)
open import Algebra.Definitions {A = R} (_≡_)


_▲_ : Op₂ R
_▲_ = curry ▲
```

```
▲-identityˡ : LeftIdentity is= _▲_
▲-identityˡ _ = refl

▲-identityʳ : RightIdentity is= _▲_
▲-identityʳ is= = refl
▲-identityʳ is< = refl
▲-identityʳ is> = refl

▲-identity : Identity is= _▲_
▲-identity =  ▲-identityˡ , ▲-identityʳ

▲-assoc : Associative _▲_
▲-assoc is= _ _ = refl
▲-assoc is< _ _ = refl
▲-assoc is> _ _ = refl

▲-isMagma : IsMagma _▲_
▲-isMagma = record { isEquivalence = isEquivalence; ∙-cong = cong₂ _▲_  }

▲-isSemigroup : IsSemigroup _▲_
▲-isSemigroup = record { isMagma = ▲-isMagma; assoc = ▲-assoc }

▲-isMonoid : IsMonoid _▲_ is=
▲-isMonoid = record { isSemigroup = ▲-isSemigroup; identity = ▲-identity }
```

The monoid we have just defined will come in handy but only once we
get to the stage of combining primitive comparison circuits
together. But before we do that we will need just such a primitive
comparison circuit.

## 1-bit comparison functions

We do that by refining `𝔽-compare` down to a 1-bit compare function.

However, before we do that I'll introduce some more abstract
definitions that will allow us to refine from `𝔽-compare` down to an
arbitrary circuit.

### Abstract comparison functions

There are (infinite) ways we can refine from `𝔽-compare` to a concrete `compare` function.
This is captured the extended commutative tower below:


                ℕ² --- ℕ-compare ----> R
                ^                      ^
                |                      |
               toℕ²                    id
                |                      |
               𝔽² k,k --- 𝔽-compare --> R
                ^                      ^
                |                      |
              μ ⊗ μ                    ν
                |                      |
              τ × τ  --- compare ----> ρ

Function `μ` is a meaning function that maps from a value of an arbitrary type
`τ` back to a finite set of size `k`, while `ν` is a meaning function which
maps from an arbitrary `ρ` type to the `R` type.

We will want to prove that this diagram commutes for many different
`μ` and `ν` values so we introduce a function `is-compare` that yields
the proposition we wish to prove.

```
is-compare : {ρ τ : Set} {k : ℕ} (μ : τ → 𝔽 k) (ν : ρ → R) (compare : τ × τ → ρ) → Set
is-compare μ ν compare = ν ∘ compare ≗ 𝔽-compare ∘ (μ ⊗ μ)
```

We also introduce a new record, `Comparison`, which contains as its
fields a `compare` function and the proof that it is a compare
function (i.e. satisfies `is-compare μ ν compare`).

```
record Comparison {ρ τ : Set} {k : ℕ} (μ : τ → 𝔽 k) (ν : ρ → R): Set where
  constructor _⊣_
  field
    compare : τ × τ → ρ
    is : is-compare μ ν compare

  𝔽-compare-sim-proof : μ ⊗ μ ⇉ ν
  𝔽-compare-sim-proof = arr compare 𝔽-compare is

  sim-proof : toℕ² ∘ (μ ⊗ μ) ⇉ ν
  sim-proof = 𝔽-compare⇉ ◎ 𝔽-compare-sim-proof
```

Note the definition of `sim-proof` which generates the SIM Proof for
the comparison function with respect to `ℕ-compare`, and
`𝔽-compare-sim-proof` which just does it with respect to `𝔽-compare`.

### Comparing single bits

We know that we want to compare single bits but, at this point, it is
not clear what would be the best type to represent `R` with. In fact,
this question may not have a definitive answer. Accordingly we set `τ
= 𝔹` and `μ = 𝔹-to-𝔽2`, but we leave `ρ` and `ν` abstract.

We are on our way to defining a function called `mk-𝔹-Comparison`
which, given a `ν` will produce a value of type `Comparison 𝔹-to-𝔽2
ν`. As it turns out, in order to prove the requisite properties we
will require more than just `ν` to be provided. We also require `ν⁻¹`
and a proof of right invertibility i.e. `ν ∘ ν⁻¹ ≗ id`.

A convenient way to do this is to package up these three things into a Agda record type.

```
record R-Rep (ρ : Set) : Set where
  field
    ν   : ρ → R
    ν⁻¹ : R → ρ
    right-invertible : ν ∘ ν⁻¹ ≗ id
    -- ρ can have redundant values that map to the 3 values of R
    -- however this means it's not left invertible. i.e.  it is not true that ν⁻¹ ∘ ν ≗ id
```

By consulting the definition of `𝔽-compare` above we can partially
refine it. Because we are refining from `𝔽-compare` specialised to
type `𝔽 2` the recursive case of the definition with pattern
`𝔽-compare (suc m) (suc n)` can only match `suc zero` which is
represented by the value `𝕥`. The right-hand side of that case "strips
the `suc`s off" yielding `𝔹-compare-ρ rr (𝕗 , 𝕗)`.

```
𝔹-compare-ρ₀ : {ρ : Set} → (nu : R-Rep ρ) → 𝔹² → ρ
𝔹-compare-ρ₀ rr (𝕗 , 𝕗) = (R-Rep.ν⁻¹ rr) is=
𝔹-compare-ρ₀ rr (𝕗 , 𝕥) = (R-Rep.ν⁻¹ rr) is<
𝔹-compare-ρ₀ rr (𝕥 , 𝕗) = (R-Rep.ν⁻¹ rr) is>
𝔹-compare-ρ₀ rr (𝕥 , 𝕥) = 𝔹-compare-ρ₀ rr (𝕗 , 𝕗)
```

But we can further simplify this via equational reasoning to:

```
𝔹-compare-ρ : {ρ : Set} → (nu : R-Rep ρ) → 𝔹² → ρ
𝔹-compare-ρ rr (𝕗 , 𝕗) = (R-Rep.ν⁻¹ rr) is=
𝔹-compare-ρ rr (𝕗 , 𝕥) = (R-Rep.ν⁻¹ rr) is<
𝔹-compare-ρ rr (𝕥 , 𝕗) = (R-Rep.ν⁻¹ rr) is>
𝔹-compare-ρ rr (𝕥 , 𝕥) = (R-Rep.ν⁻¹ rr) is=
```

Next we define a function that specialise `is-compare` to `τ = 𝔹`.


```
is-𝔹-compare : {ρ : Set} → (rr : R-Rep ρ) → Set
is-𝔹-compare rr = is-compare 𝔹-to-𝔽2 (R-Rep.ν rr) (𝔹-compare-ρ rr)
```

We can now create two `R-Rep` values for the case where `R` is
represented by `𝔹²` and ‵𝔹³` respectively. The proofs of right
invertibility are straightforward and done by exhaustion.

```
𝔹²-rr : R-Rep 𝔹²
𝔹²-rr = record { ν = 𝔹²-to-R ; ν⁻¹ = R-to-𝔹² ; right-invertible = λ { is< → refl ; is= → refl ; is> → refl } }

𝔹³-rr : R-Rep 𝔹³
𝔹³-rr = record { ν = 𝔹³-to-R ; ν⁻¹ = R-to-𝔹³ ; right-invertible = λ { is< → refl ; is= → refl ; is> → refl } }
```

Given a value `rr : R-Rep ρ` we can prove `is-𝔹-compare rr` using the following
reasoning:

```
rr-to-is-𝔹-compare : {ρ : Set} → (rr : R-Rep ρ) → is-𝔹-compare rr
rr-to-is-𝔹-compare rr =
    λ { f,f@(𝕗 , 𝕗) → p {f,f} {is=} refl refl
      ; f,t@(𝕗 , 𝕥) → p {f,t} {is<} refl refl
      ; t,f@(𝕥 , 𝕗) → p {t,f} {is>} refl refl
      ; t,t@(𝕥 , 𝕥) → p {t,t} {is=} refl refl
      }

  where
    open ≡-Reasoning
    p : ∀ {a b}
        → 𝔹-compare-ρ rr a ≡ R-Rep.ν⁻¹ rr b
        → b ≡ 𝔽-compare ((𝔹-to-𝔽2 ⊗ 𝔹-to-𝔽2) a)
        → R-Rep.ν rr (𝔹-compare-ρ rr a) ≡ 𝔽-compare ((𝔹-to-𝔽2 ⊗ 𝔹-to-𝔽2) a)
    p {a} {b} eq eq2 =
      begin
        R-Rep.ν rr (𝔹-compare-ρ rr a)
      ≡⟨ cong (R-Rep.ν rr) eq ⟩
        (R-Rep.ν rr ∘ R-Rep.ν⁻¹ rr) b
      ≡⟨ R-Rep.right-invertible rr b ⟩
        id b
      ≡⟨⟩
        b
      ≡⟨ eq2 ⟩
        𝔽-compare ((𝔹-to-𝔽2 ⊗ 𝔹-to-𝔽2) a)
      ∎
```

We can now complete the definition of `mk-𝔹-Comparison`.

```
mk-𝔹-Comparison : {ρ : Set} → (rr : R-Rep ρ) → Comparison 𝔹-to-𝔽2 (R-Rep.ν rr)
mk-𝔹-Comparison {ρ} rr = 𝔹-compare-ρ rr ⊣ (rr-to-is-𝔹-compare rr)
```

We can now plug in the two `R-Rep` values we defined above to generate
comparison functions _along with their proofs_.


```
𝔹-Comparison-𝔹² : Comparison 𝔹-to-𝔽2 𝔹²-to-R
𝔹-Comparison-𝔹² = mk-𝔹-Comparison 𝔹²-rr

𝔹-Comparison-𝔹³ : Comparison 𝔹-to-𝔽2 𝔹³-to-R
𝔹-Comparison-𝔹³ = mk-𝔹-Comparison 𝔹³-rr
```

## And now for the combinators

        R × R ----- ▲ ------> R
          ^                   ^
          |                   |
        ν ⊗ ν                 ν
          |                   |
          |                   |
        ρ × ρ ----- △ ------> ρ


```
is-monoid-op : {ρ : Set} → (ρ → R) → (△ : ρ × ρ → ρ) → Set
is-monoid-op ν △ = ▲ ∘ (ν ⊗ ν) ≗ ν ∘ △
```


```
comb : ∀ {(m , n) : ℕ²} → 𝔽² (m , n) → 𝔽 (n * m)
comb = uncurry combine ∘ swap

_●_ : ∀ {τₘ τₙ} {(m , n) : ℕ²} (μₘ : τₘ → 𝔽 m) (μₙ : τₙ → 𝔽 n)
    → (τₘ × τₙ → 𝔽 (n * m))
μₘ ● μₙ = comb ∘ (μₘ ⊗ μₙ)

D : Set → Set → Set
D ρ τ = τ × τ → ρ

mk-●̂ : ∀ {ρ τₘ τₙ} → (ρ × ρ → ρ) → D ρ τₘ → D ρ τₙ → D ρ (τₘ × τₙ)
mk-●̂ op compareₘ compareₙ  ((aₘ , aₙ)  , (bₘ , bₙ)) =
  let ρ₁ = compareₘ (aₘ , bₘ)
      ρ₂ = compareₙ (aₙ , bₙ)
  in op (ρ₁ , ρ₂)
```

Now let's try to define a 2-bit comparison.

```
opᴮ₀ : 𝔹² × 𝔹² → 𝔹²
opᴮ₀ ((𝕥 , b) , r₂) = (𝕥 , b)
opᴮ₀ ((𝕗 , 𝕗) , r₂) = (𝕗 , 𝕗)
opᴮ₀ ((𝕗 , 𝕥) , r₂) = r₂

opᴮ : 𝔹² × 𝔹² → 𝔹²
opᴮ = cond ∘ ((exl ∘ exl) ▵ else ▵ exl)
  where
    else : 𝔹² × 𝔹² → 𝔹²
    else = cond ∘ ((not ∘ ∨ ∘ exl) ▵ exr  ▵ exl)

opᴮ≗opᴮ₀ : opᴮ ≗ opᴮ₀
opᴮ≗opᴮ₀ = λ { ((𝕗 , 𝕗) , _) →  refl
             ; ((𝕗 , 𝕥) , _) →  refl
             ; ((𝕥 , 𝕗) , _) →  refl
             ; ((𝕥 , 𝕥) , _) →  refl
             }
```

Let's see if we can show it's a monoid op.

```
opᴮ-is-monoid-op : is-monoid-op 𝔹²-to-R opᴮ
opᴮ-is-monoid-op = λ { ((𝕗 , 𝕗) , _) → refl
                     ; ((𝕗 , 𝕥) , _) → refl
                     ; ((𝕥 , _) , _) → refl
                     }
```

Now let's try it with comparison function with three values.

```
opᴮ³ : 𝔹³ × 𝔹³ → 𝔹³
opᴮ³ ((𝕥 , _ , _) , r₂) = (𝕥 , 𝕗 , 𝕗)
opᴮ³ ((𝕗 , 𝕥 , _) , r₂) = r₂
opᴮ³ ((𝕗 , 𝕗 , 𝕥) , r₂) = (𝕗 , 𝕗 , 𝕥)
opᴮ³ ((𝕗 , 𝕗 , 𝕗) , r₂) = (𝕥 , 𝕗 , 𝕗)

opᴮ³-is-monoid-op : is-monoid-op 𝔹³-to-R opᴮ³
opᴮ³-is-monoid-op = λ { ((𝕥 , _ , _) , _) → refl
                      ; ((𝕗 , 𝕥 , _) , _) → refl
                      ; ((𝕗 , 𝕗 , 𝕥) , _) → refl
                      ; ((𝕗 , 𝕗 , 𝕗) , _) → refl
                      }
```



```
𝔹²-compare : 𝔹² × 𝔹² → 𝔹²
𝔹²-compare = 𝔹-compare-𝔹² ●̂ 𝔹-compare-𝔹²
  where
    _●̂_ : ∀ {τₘ τₙ} → D 𝔹² τₘ → D 𝔹² τₙ  → D 𝔹² (τₘ × τₙ)
    _●̂_ = mk-●̂ opᴮ
```

And now a 4-bit comparison.

```
𝔹⁴-compare : (𝔹² × 𝔹²) × (𝔹² × 𝔹²) → 𝔹²
𝔹⁴-compare = (𝔹-compare-𝔹² ●̂ 𝔹-compare-𝔹²) ●̂ (𝔹-compare-𝔹² ●̂ 𝔹-compare-𝔹²)
  where
    _●̂_ : ∀ {τₘ τₙ} → D 𝔹² τₘ → D 𝔹² τₙ  → D 𝔹² (τₘ × τₙ)
    _●̂_ = mk-●̂ opᴮ

```

## The diagrams

```
open import Ty
open import Categorical.Free.Homomorphism Function renaming (_⇨_ to _↦_)

open import Categorical.Homomorphism
  renaming ( refl to ≈refl; trans to ≈trans; sym to ≈sym
           ; Bool to 𝔹̂; ∧ to ⟨∧⟩; ∨ to ⟨∨⟩; xor to ⟨⊕⟩
           )

D̂ : Ty → Ty → Set
D̂ ρ τ = τ × τ ↦ ρ

𝔹̂² : Ty
𝔹̂² = 𝔹̂ × 𝔹̂

𝔹-compareC : 𝔹̂² ↦ 𝔹̂²
𝔹-compareC = (∧ ∘ first not) ▵ (not ∘ xor)

mk-■̂ : ∀ {ρ τₘ τₙ} → (ρ × ρ ↦ ρ) → D̂ ρ τₘ → D̂ ρ τₙ → D̂ ρ (τₘ × τₙ)
mk-■̂ op compareₘ compareₙ = op ∘ (compareₘ ⊗ compareₙ) ∘ transpose

opᴮ̂ : 𝔹̂² × 𝔹̂² ↦ 𝔹̂²
opᴮ̂ = cond ∘ ((exl ∘ exl) ▵ else ▵ exl)
  where
    else : 𝔹̂² × 𝔹̂² ↦ 𝔹̂²
    else = cond ∘ ((not ∘ ∨ ∘ exl) ▵ exr  ▵ exl)

𝔹⁴-compareC : (𝔹̂² × 𝔹̂²) × (𝔹̂² × 𝔹̂²) ↦ 𝔹̂²
𝔹⁴-compareC = (𝔹-compareC ■̂ 𝔹-compareC) ■̂ (𝔹-compareC ■̂ 𝔹-compareC)
  where
    _■̂_ : ∀ {τₘ τₙ} → D̂ 𝔹̂² τₘ → D̂ 𝔹̂² τₙ  → D̂ 𝔹̂² (τₘ × τₙ)
    _■̂_ = mk-■̂ opᴮ̂

Fₘ-𝔹⁴-compareᶜC : Fₘ 𝔹⁴-compareC ≡ 𝔹⁴-compare
Fₘ-𝔹⁴-compareᶜC  = refl
```

```
open import Level using (0ℓ)
open import IO
open import Data.String hiding (_≟_)

open import Primitive.Raw Function renaming (_⇨_ to _⇨ₚ_)
open import Routing.Raw renaming (_⇨_ to _⇨ᵣ_)
open import Linearize.Raw Function _⇨ₚ_ _⇨ᵣ_ renaming (_⇨_ to _↠_)

import Categorical.Free.Homomorphism _↠_ as FL
import Test as T

example : ∀ {a b : Ty} → String → (c : a ↦ b) → IO {0ℓ} _
example name c = T.example name (Fₘ c)

main = run do
  example "boolean-compare" 𝔹-compareC
  example "4-bit-compare" 𝔹⁴-compareC
```


## Appendix


### Representing the `R` type using booleans and dependent products

I mentioned earlier that there was a little redundancy in representing
the `R` type using `𝔹²` and a lot of redundancy representing it with
`𝔹³`. In this section I present a way to represent `R` in `𝔹³` with no
redundancy by using a dependent product. The first element of the
dependent product is just `𝔹³` while the second element is a proof
that the triple is "one-hot" which means that precisely one of the
boolean values in the triple is true while the rest are false.

The function `hotness` returns the number of `𝕥` values in the triple
and can range from 0 to 3.

```
open import Data.Product using (Σ)

hotness : 𝔹 × 𝔹 × 𝔹 → ℕ
hotness (b₁ , b₂ , b₃) = val b₁ + val b₂ + val b₃
  where
    val : 𝔹 → ℕ
    val 𝕗 = 0
    val 𝕥 = 1
```

We then define the dependent product. The _type_ of the second element
depends on the _value_ of the first. For example if the _value_ of the
first element is `(𝕥 , 𝕗 , 𝕗)` then the _type_ of the second element
is `hotness (𝕥 , 𝕗 , 𝕗) ≡ 1`.

```
Σ𝔹³ : Set
Σ𝔹³ = Σ 𝔹³ (λ x → hotness x ≡ 1)
```

We can then define the conversion functions to and from `Σ𝔹³`.

```
Σ𝔹³-to-R : Σ𝔹³ → R
Σ𝔹³-to-R ((𝕥 , 𝕗 , 𝕗) , refl) = is<
Σ𝔹³-to-R ((𝕗 , 𝕥 , 𝕗) , refl) = is=
Σ𝔹³-to-R ((𝕗 , 𝕗 , 𝕥) , refl) = is>

R-to-Σ𝔹³ : R → Σ𝔹³
R-to-Σ𝔹³ is< = ( (𝕥 , 𝕗 , 𝕗) , refl)
R-to-Σ𝔹³ is= = ( (𝕗 , 𝕥 , 𝕗) , refl)
R-to-Σ𝔹³ is> = ( (𝕗 , 𝕗 , 𝕥) , refl)
```

Pleasingly, using this representation, we can prove invertibility in
both directions.

```
Σ𝔹³-to-R∘R-to-Σ𝔹³ : Σ𝔹³-to-R ∘ R-to-Σ𝔹³ ≗ id
Σ𝔹³-to-R∘R-to-Σ𝔹³ is<  = refl
Σ𝔹³-to-R∘R-to-Σ𝔹³ is=  = refl
Σ𝔹³-to-R∘R-to-Σ𝔹³ is>  = refl

R-to-Σ𝔹∘Σ𝔹³-to-R : R-to-Σ𝔹³ ∘ Σ𝔹³-to-R ≗ id
R-to-Σ𝔹∘Σ𝔹³-to-R ( (𝕥 , 𝕗 , 𝕗) , refl) = refl
R-to-Σ𝔹∘Σ𝔹³-to-R ( (𝕗 , 𝕥 , 𝕗) , refl) = refl
R-to-Σ𝔹∘Σ𝔹³-to-R ( (𝕗 , 𝕗 , 𝕥) , refl) = refl
```

However, I don't yet know how to make this work with Conal's work on
Compiling to Categories. This is an open problem at this point.
