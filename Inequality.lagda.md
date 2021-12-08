<!-- -*-agda2-*- -->

<!--
```
{-# OPTIONS --guardedness #-}  -- For tesing/IO
module Inequality where

open import Relation.Binary.Core using (Rel)
open import Data.Bool renaming (Bool to 𝔹) hiding (_≤_;not;_∧_; true; false)
open import Data.Bool.Properties
open import Data.Nat hiding (_≤_ ; _≤ᵇ_;_≟_; compare; _⊔_)
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

# Deriving comparison circuits via Denotational Design

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

```agda
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


```agda
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


```agda
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

```agda
toℕ² : {i,j : ℕ²} → 𝔽² i,j → ℕ²
toℕ² (m , n) = (toℕ m , toℕ n)
```

Let's start with a trivial proof of the commutativity of the
diagram. The type of `toℕ²` so closely follows the body of `𝔽≤` that
we can just use `refl`.

```agda
toℕ-≤ : {i,j : ℕ²} → 𝔽≤ {i,j} ≗ ℕ≤ ∘ toℕ²
toℕ-≤ _ = refl
```

Let's now encapsulate that proof using an instance of an _arrow category_.

```agda
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

```agda
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


```agda
data R : Set where
  is< : R
  is= : R
  is> : R
```

This has some immediate implications. First, in order to define a
less-than-or-equal function which returns a boolean we will now
require an auxillary function of type `R → 𝔹`. Fortunately, this
is trivial to define.

```agda
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

```agda
𝔽-compare : {i,j : ℕ²} → 𝔽² i,j → R
𝔽-compare (zero , zero)    = is=
𝔽-compare (zero , suc _)   = is<
𝔽-compare (suc _ , zero)   = is>
𝔽-compare (suc m , suc n)  = 𝔽-compare (m , n)
```

We also define an equivalent function on ℕ and prove a correspondence
between the two.

```agda
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

```agda
toℕ²-ℕ-compare : {i,j : ℕ²} → 𝔽-compare {i,j} ≗ ℕ-compare ∘ toℕ²
toℕ²-ℕ-compare (zero  , zero)  = refl
toℕ²-ℕ-compare (zero  , suc _) = refl
toℕ²-ℕ-compare (suc _ , zero)  = refl
toℕ²-ℕ-compare (suc m , suc n) = toℕ²-ℕ-compare (m , n)
```

We package this up as a SIM Proof as follows:

```agda
𝔽-compare⇉ : {i,j : ℕ²} → toℕ² {i,j} ⇉ id
𝔽-compare⇉  = arr 𝔽-compare ℕ-compare toℕ²-ℕ-compare
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
    ≡ g         where g = e ⊕ f

[TODO: Use the term "parallel call-by-value]

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
called `⟨▲⟩`.

```agda
⟨▲⟩ : R × R → R
⟨▲⟩ (is= , r₂) = r₂
⟨▲⟩ (is< , _)  = is<
⟨▲⟩ (is> , _)  = is>
```

By considering every pair of possible inputs (for a total of 9 cases)
one can convince oneself that this operator is associative and that
`is=` is the identity element. However, we can gain even more
assurance by proving this in Agda.

To do this we use the Standard Library's `Algebra` modules. This
requires we uncurry the `⟨▲⟩` operator as their definitions are only
defined in terms of uncurried functions.

```agda
module _▲_-proofs where
  open import Algebra.Core
  open import Algebra.Structures {A = R} (_≡_)
  open import Algebra.Definitions {A = R} (_≡_)


  _▲_ : Op₂ R
  _▲_ = curry ⟨▲⟩
```

```agda
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

```agda
is-compare : {ρ τ : Set} {k : ℕ} (μ : τ → 𝔽 k) (ν : ρ → R) (compare : τ × τ → ρ) → Set
is-compare μ ν compare = ν ∘ compare ≗ 𝔽-compare ∘ (μ ⊗ μ)
```

We also introduce a new record, `Comparison`, which contains as its
fields a `compare` function and the proof that it is a compare
function (i.e. satisfies `is-compare μ ν compare`).

```agda
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

## Bits represent Finite Sets of cardinality 2

A finite set of cardinality 2 (`𝔽 2`) can be represented by a single
bit. Accordingly we define two functions to convert to and from bits.

```agda
F𝟚-to-𝔹 : 𝔽 2 → 𝔹
F𝟚-to-𝔹 zero       = 𝕗
F𝟚-to-𝔹 (suc zero) = 𝕥

𝔹-to-𝔽2 : 𝔹 → 𝔽 2
𝔹-to-𝔽2 𝕗 = zero
𝔹-to-𝔽2 𝕥 = suc zero
```

We also prove that they are inverses of each other

```agda
F𝟚-to-𝔹∘𝔹-to-𝔽2≗ : F𝟚-to-𝔹 ∘ 𝔹-to-𝔽2 ≗ id
F𝟚-to-𝔹∘𝔹-to-𝔽2≗ = λ { 𝕥 → refl; 𝕗 → refl }

𝔹-to-𝔽2∘F𝟚-to-𝔹≗id : 𝔹-to-𝔽2 ∘ F𝟚-to-𝔹 ≗ id
𝔹-to-𝔽2∘F𝟚-to-𝔹≗id = λ { zero → refl; (suc zero) → refl }
```

### Comparing bits but leaving the representation of `R` abstract

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

```agda
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

```agda
𝔹-compare-ρ₀ : {ρ : Set} → (nu : R-Rep ρ) → 𝔹² → ρ
𝔹-compare-ρ₀ rr (𝕗 , 𝕗) = (R-Rep.ν⁻¹ rr) is=
𝔹-compare-ρ₀ rr (𝕗 , 𝕥) = (R-Rep.ν⁻¹ rr) is<
𝔹-compare-ρ₀ rr (𝕥 , 𝕗) = (R-Rep.ν⁻¹ rr) is>
𝔹-compare-ρ₀ rr (𝕥 , 𝕥) = 𝔹-compare-ρ₀ rr (𝕗 , 𝕗)
```

But we can further simplify this via equational reasoning to:

```agda
𝔹-compare-ρ : {ρ : Set} → R-Rep ρ → 𝔹² → ρ
𝔹-compare-ρ rr (𝕗 , 𝕗) = (R-Rep.ν⁻¹ rr) is=
𝔹-compare-ρ rr (𝕗 , 𝕥) = (R-Rep.ν⁻¹ rr) is<
𝔹-compare-ρ rr (𝕥 , 𝕗) = (R-Rep.ν⁻¹ rr) is>
𝔹-compare-ρ rr (𝕥 , 𝕥) = (R-Rep.ν⁻¹ rr) is=
```

Next we define a function that specialise `is-compare` to `τ = 𝔹`.


```agda
is-𝔹-compare : {ρ : Set} → (rr : R-Rep ρ) → Set
is-𝔹-compare rr = is-compare 𝔹-to-𝔽2 (R-Rep.ν rr) (𝔹-compare-ρ rr)
```

## Two representations of `R`

Most modern hardware restricts itself to representing values only
using bits. One can represent any type with `2ⁿ` values via a
collection of bits but, conversely, if you are trying to represent a
type that doesn't have exactly this many values then there will be
some redundancy in the encoding. Whether there is a better way to
encode values in hardware, perhaps using different bases, or more
complicated circuitry is an open question that I would like to explore
further in future. However, for the purposes of this note I will use
the standard techniques modern hardware uses.

### A two-bit encoding of `R`

The encoding for `R` with the _least redundancy_ is a pair of bits
(`𝔹²`). This type has 4 values while `R` has only 3 so their will be
one redundant value. There are many ways to encode `R` using `𝔹²` but
we choose and encoding where each element of the pair means
something. The first element represents whether the value is `is<` and
the second whether the value is `is=`. This gives us:

```agda
R-to-𝔹² : R → 𝔹²
R-to-𝔹² is< = (𝕥 , 𝕗)
R-to-𝔹² is= = (𝕗 , 𝕥)
R-to-𝔹² is> = (𝕗 , 𝕗)
```

The missing value of `𝔹²` on the right hand side is `(𝕥 ,
𝕥)`. Fortunately, this value would be meaningless since two numbers
cannot both be less-than and equal to each other. Nevertheless, the
redundancy of the `𝔹²` type in representing `R` values does not sit
well with me, and seems inelegant. The non-redundant representation of
sum types like `R` is still an open problem in want of a solution.

We want `R-to-𝔹²` to be invertible but this leads us to the question
of what we should do with the input `(𝕥 , 𝕥)`. One choice is that it
represents `is<` if we slightly modify the meaning of the pair of
booleans to mean that the second component only has a meaning if the
first component is `𝕗`. This leads to this definition:


```agda
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

### The "one-hot" three-bit-encoding of `R`

## 3-bit representation of `R`

It seems common in traditional hardware design to use a "one-hot"
3-bit representation of the `R` type. That is, three wires only one of
which can be true, the rest being false.

```agda
𝔹³ : Set
𝔹³ = 𝔹 × 𝔹 × 𝔹
```

Defining `R-to-𝔹³` is straightforward.

```agda
R-to-𝔹³ : R → 𝔹³
R-to-𝔹³ is< = (𝕥 , 𝕗 , 𝕗)
R-to-𝔹³ is= = (𝕗 , 𝕥 , 𝕗)
R-to-𝔹³ is> = (𝕗 , 𝕗 , 𝕥)
```

However, the inverse function is even trickier to define than
`𝔹²-to-R`. We want a total function but there is a even more
redundancy in the representation than for the 2-bit case since 3 bits
can represent 8 different values. We must have cases for when there is
more than "one hot wire" and we must also consider the case where none
of them are "hot".

We choose `is<` as our "no hot" case and use a priority-based encoding
for the other cases.  Each of the positions in the triple denote
`is<`, `is=` and `is>` respectively, but this is also the order of
priority.

If a `𝕥` appears in the `is<` position then it overrides whatever is
in the other two positions.  The `is=` is similar. It has priority
over the `is>` value but only when an `𝕗` appears in the `is<`
position. This leads us to the following definition:


```agda
𝔹³-to-R : 𝔹³ → R
𝔹³-to-R (𝕗 , 𝕗 , 𝕗) = is<
𝔹³-to-R (𝕥 , _ , _) = is<
𝔹³-to-R (𝕗 , 𝕥 , _) = is=
𝔹³-to-R (𝕗 , 𝕗 , 𝕥) = is>
```

## Two one-bit comparison functions with different representations for `R`

We can now create two `R-Rep` values for the case where `R` is
represented by `𝔹²` and ‵𝔹³` respectively. The proofs of right
invertibility are straightforward and done by exhaustion.

```agda
𝔹²-rr : R-Rep 𝔹²
𝔹²-rr = record { ν = 𝔹²-to-R ; ν⁻¹ = R-to-𝔹² ; right-invertible = λ { is< → refl ; is= → refl ; is> → refl } }

𝔹³-rr : R-Rep 𝔹³
𝔹³-rr = record { ν = 𝔹³-to-R ; ν⁻¹ = R-to-𝔹³ ; right-invertible = λ { is< → refl ; is= → refl ; is> → refl } }
```

Given a value `rr : R-Rep ρ` we can prove `is-𝔹-compare rr` using the following
reasoning:

```agda
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

```agda
mk-𝔹-Comparison : {ρ : Set} → (rr : R-Rep ρ) → Comparison 𝔹-to-𝔽2 (R-Rep.ν rr)
mk-𝔹-Comparison {ρ} rr = 𝔹-compare-ρ rr ⊣ (rr-to-is-𝔹-compare rr)
```

We can now plug in the two `R-Rep` values we defined above to generate
comparison functions _along with their proofs_.


```agda
𝔹-Comparison-𝔹² : Comparison 𝔹-to-𝔽2 𝔹²-to-R
𝔹-Comparison-𝔹² = mk-𝔹-Comparison 𝔹²-rr

𝔹-Comparison-𝔹³ : Comparison 𝔹-to-𝔽2 𝔹³-to-R
𝔹-Comparison-𝔹³ = mk-𝔹-Comparison 𝔹³-rr
```

## Switching to categorical representation of comparison functions

While the principles of "compiling to categories" (TODO: Add
reference!) are now well-understood, the implementation of a function
that can automatically do this is not quite finished at the time I'm
writing this.

Thus, for the rest of this note I will use explicitly define functions
using a categorical representation and, where necessary, "compile by
hand" the definitions we have already come up with to this
representation.

### Some necessary abbreviations

```agda
open import Ty
open import Categorical.Free.Homomorphism Function

open import Categorical.Homomorphism
  renaming ( refl to ≈refl; trans to ≈trans; sym to ≈sym
           ; Bool to 𝔹̂; ∧ to ⟨∧⟩; ∨ to ⟨∨⟩; xor to ⟨⊕⟩
           )
𝔹̂² : Ty
𝔹̂² = 𝔹̂ × 𝔹̂

𝔹̂³ : Ty
𝔹̂³ = 𝔹̂ × 𝔹̂ × 𝔹̂
```

## Hand-compiling down to categorical representation for `𝔹-compare-𝔹²`

We have already defined the comparison function which uses `𝔹²` as its
representation type for `R`. It is the `compare` field of record value
`𝔹-Comparison-𝔹²`.

We'll start the hand-compilation process by writing down an equivalent
function `𝔹-compare-𝔹²₀`. We do this by consulting the definition of
`𝔹-compare-ρ` and `R-to-𝔹²`. We get:

```agda
𝔹-compare-𝔹²₀ : 𝔹² → 𝔹²
𝔹-compare-𝔹²₀ (𝕗 , 𝕗) = (𝕗 , 𝕥)
𝔹-compare-𝔹²₀ (𝕗 , 𝕥) = (𝕥 , 𝕗)
𝔹-compare-𝔹²₀ (𝕥 , 𝕗) = (𝕗 , 𝕗)
𝔹-compare-𝔹²₀ (𝕥 , 𝕥) = (𝕗 , 𝕥)
```

Next, we separate `𝔹-compare-𝔹²₀` into two functions and use the `▵`
operator to combine the results again.

```agda
𝔹-compare-𝔹²₁ : 𝔹² → 𝔹²
𝔹-compare-𝔹²₁ = comp-fst ▵ comp-snd
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

The next part of the hand-compilation process relies on familiarity
with the standard binary boolean functions and their truth tables. The
RHS of `comp-fst` is only true in one case which is very similar to
the `⟨∧⟩` function. By applying `not` to the first component of the
input pair before applying `⟨∧⟩` we get a function definitonally
equivalent to `comp-fst`.

In the second case the output looks just like `not ∘ ⟨⊕⟩`.

I will define the function using `𝔹̂` and the categorical arrow `_⇨_`
since it now contains categorical primitives only.


```agda
𝔹̂-compare-𝔹̂² : 𝔹̂² ⇨ 𝔹̂²
𝔹̂-compare-𝔹̂² = (⟨∧⟩ ∘ first not) ▵ (not ∘ ⟨⊕⟩)
```

Just to be sure we check that its image under `Fₘ` is the same as the
original comparison function we defined. In this particular case, `Fₘ`
maps from the category of syntax to the category of functions.

```agda
𝔹̂-compare-𝔹̂²≗𝔹-compare-𝔹² : Fₘ 𝔹̂-compare-𝔹̂² ≗ Comparison.compare 𝔹-Comparison-𝔹²
𝔹̂-compare-𝔹̂²≗𝔹-compare-𝔹² =
  λ { (𝕗 , 𝕗) → refl
    ; (𝕗 , 𝕥) → refl
    ; (𝕥 , 𝕗) → refl
    ; (𝕥 , 𝕥) → refl
    }
```

## The categorical representation of `𝔹̂-compare-𝔹̂³`

I will leave the details of how to compile down to `𝔹̂-compare-𝔹̂³` as
an exercise for you, dear reader. The result is similar to that for `𝔹̂-compare-𝔹̂²`.

```agda
𝔹̂-compare-𝔹̂³ : 𝔹̂² ⇨ 𝔹̂³
𝔹̂-compare-𝔹̂³ = (⟨∧⟩ ∘ first not) ▵ (not ∘ ⟨⊕⟩) ▵ (∧ ∘ second not)

𝔹̂-compare-𝔹̂³≗𝔹-compare-𝔹³ : Fₘ 𝔹̂-compare-𝔹̂³ ≗ Comparison.compare 𝔹-Comparison-𝔹³
𝔹̂-compare-𝔹̂³≗𝔹-compare-𝔹³ =
  λ { (𝕗 , 𝕗) → refl
    ; (𝕗 , 𝕥) → refl
    ; (𝕥 , 𝕗) → refl
    ; (𝕥 , 𝕥) → refl
    }

```

## Combining primitive comparison functions

In this section we return to considering generic comparison functions
that are refinements of `𝔽-compare` according to this commutative
diagram that we have seen before:

              𝔽² m,n --- 𝔽-compare --> R
                ^                      ^
                |                      |
              μ ⊗ μ                    ν
                |                      |
              τ × τ  --- compare ----> ρ


Consider two comparison functions `c₁ : τₘ × τₘ → ρ` and `c₂ : τₙ × τₙ
→ ρ` where `τₘ`, `τₙ` and ‵ρ` are arbitrary types.  In this section we
will define a combinator that can combine these two comparison
functions into a comparison function `cᵣ : (τₘ × τₙ) × (τₘ × τₙ) → ρ`.


The definition is inspired by considering multi-digit
representations. However, it is more general. Note that types `τₘ` and
`τₙ` can have different cardinality, and so this combinator could be
used in a case where each "digit" of the input representation is of a
different "base".

In order to combine two comparison functions we need to have a
way of combining their associated meaning functions which we denote
`μₘ` and `μₙ`.


```agda
⟨combine⟩ : ∀ {(m , n) : ℕ²} → 𝔽² (m , n) → 𝔽 (m * n)
⟨combine⟩ = uncurry combine

_●_ : ∀ {τₘ τₙ} {(m , n) : ℕ²} (μₘ : τₘ → 𝔽 m) (μₙ : τₙ → 𝔽 n)
    → (τₘ × τₙ → 𝔽 (m * n))
μₘ ● μₙ = ⟨combine⟩ ∘ (μₘ ⊗ μₙ)
```

Once we can combine meaning functions we can look at generating an
operator that, given two comparison functions, generates a comparison
function that takes two pairs, applies `c₁` to the first element of
each pair, `c₂` to the second element of each pair and then combines
the two resulting values of `ρ` together somehow.

But just how are these values to be combined? We can provide an
operator `⟨△⟩ : ρ × ρ → ρ` to do just that. Earlier we defined `⟨▲⟩`
and showed that `R` was a monoid under this associative binary
operator. We want exactly the same for `⟨△⟩`. That is, we want `ρ` to
be a monoid under the operator `⟨△⟩`. Further, `⟨△⟩` should be a
refinement of `⟨▲⟩` according to the following diagram. Here `ν : ρ →
R` is the meaning function for values of type ‵ρ`.

        R × R ---- ⟨▲⟩ -----> R
          ^                   ^
          |                   |
        ν ⊗ ν                 ν
          |                   |
          |                   |
        ρ × ρ ---- ⟨△⟩ -----> ρ


We define a function which generates the type signature for the proof
that the diagram above is commutative. We will use this later when
proving that combined comparison functions are still refinements of
`𝔽-compare`.

```agda
is-⟨▲⟩-refinement : {ρ : Set} → (ρ → R) → (△ : ρ × ρ → ρ) → Set
is-⟨▲⟩-refinement ν ⟨△⟩ = ⟨▲⟩ ∘ (ν ⊗ ν) ≗ ν ∘ ⟨△⟩
```

-------------------------- scratch

```agda
module ⟨△⟩-proofs {ρ : Set} where

  open import Algebra.Core
  open import Algebra.Structures  {A = ρ} (_≡_)
  open import Algebra.Definitions {A = ρ} (_≡_)
  open ≡-Reasoning

  ⟨△⟩-is-identityˡ : {ν : ρ → R} {ν⁻¹ : R → ρ} {⟨△⟩ : ρ × ρ → ρ}
                → ν ∘ ν⁻¹ ≡ id
                → ν⁻¹ ∘ ν ≡ id
                → ν⁻¹ ∘ ⟨▲⟩ ∘ (ν ⊗ ν) ≗ ⟨△⟩
                → (∀ x → ⟨△⟩ (ν⁻¹ is= , x) ≡ x)
  ⟨△⟩-is-identityˡ {ν} {ν⁻¹} {⟨△⟩} inverser inversel equiv = (λ x →
        begin
          ⟨△⟩ (ν⁻¹ is= , x)
        ≡⟨ sym (equiv (ν⁻¹ is= , x))  ⟩
          (ν⁻¹ ∘ ⟨▲⟩ ∘ (ν ⊗ ν)) (ν⁻¹ is= ,  x)
        ≡⟨⟩
          (ν⁻¹ ∘ ⟨▲⟩) ((ν ∘ ν⁻¹) is= , ν x)
        ≡⟨ cong (λ □ → (ν⁻¹ ∘ ⟨▲⟩) (□ is= , ν x)) inverser ⟩
          (ν⁻¹ ∘ ⟨▲⟩) (is= , ν x)
        ≡⟨⟩
          ν⁻¹ (⟨▲⟩ (is= , ν x))
        ≡⟨ cong (λ □ → ν⁻¹ □) (_▲_-proofs.▲-identityˡ (ν x))  ⟩
          (ν⁻¹ ∘ ν) x
        ≡⟨ cong (λ □ → □ x) inversel ⟩
          x
        ∎)


  ⟨△⟩-is-identityʳ : {ν : ρ → R} {ν⁻¹ : R → ρ} {⟨△⟩ : ρ × ρ → ρ}
                → ν ∘ ν⁻¹ ≡ id
                → ν⁻¹ ∘ ν ≡ id
                → ν⁻¹ ∘ ⟨▲⟩ ∘ (ν ⊗ ν) ≗ ⟨△⟩
                → (∀ x → ⟨△⟩ (x , ν⁻¹ is=) ≡ x)
  ⟨△⟩-is-identityʳ {ν} {ν⁻¹} {⟨△⟩} inverser inversel equiv = (λ x →
        begin
          ⟨△⟩ (x , ν⁻¹ is=)
        ≡⟨ sym (equiv (x , ν⁻¹ is=))  ⟩
          (ν⁻¹ ∘ ⟨▲⟩ ∘ (ν ⊗ ν)) (x , ν⁻¹ is=)
        ≡⟨⟩
          (ν⁻¹ ∘ ⟨▲⟩) (ν x , (ν ∘ ν⁻¹) is=)
        ≡⟨ cong (λ □ → ((ν⁻¹ ∘ ⟨▲⟩) (ν x , □ is=))) inverser ⟩
          (ν⁻¹ ∘ ⟨▲⟩) (ν x , is=)
        ≡⟨⟩
          ν⁻¹ (⟨▲⟩ (ν x , is=))
        ≡⟨ cong (λ □ → ν⁻¹ □) (_▲_-proofs.▲-identityʳ (ν x))  ⟩
          (ν⁻¹ ∘ ν) x
        ≡⟨ cong (λ □ → □ x) inversel ⟩
          x
        ∎)
```
----------------------------- scratch


Now we can look at defining our combinator. For convenience we also
define a type synonym `D`.

```agda
D : Set → Set → Set
D τ ρ = τ × τ → ρ

mk-●̂ : ∀ {ρ τₘ τₙ} → (ρ × ρ → ρ) → D τₘ ρ → D τₙ ρ → D (τₘ × τₙ) ρ
mk-●̂ ⟨△⟩ compareₘ compareₙ = λ ((aₘ , aₙ)  , (bₘ , bₙ)) →
  let ρ₁ = compareₘ (aₘ , bₘ)
      ρ₂ = compareₙ (aₙ , bₙ)
  in ⟨△⟩ (ρ₁ , ρ₂)
```

In categorical terms this can be defined as follows. We use the `■`
symbol as an analogue of the `●` symbol whenever we are expressing
definitions using a categorical representation.

```agda
D̂ : Ty → Ty → Set
D̂ τ ρ = τ × τ ⇨ ρ

mk-■̂ : ∀ {ρ τₘ τₙ} → (ρ × ρ ⇨ ρ) → D̂ τₘ ρ → D̂ τₙ ρ → D̂ (τₘ × τₙ) ρ
mk-■̂ ⟨△⟩ compareₘ compareₙ = ⟨△⟩ ∘ (compareₘ ⊗ compareₙ) ∘ transpose
```

## A combinator for the `𝔹²` representation of `R`

In this section we attempt to refine `⟨▲⟩` to `⟨△-𝔹²⟩ : 𝔹² × 𝔹² → 𝔹²`

By carefully looking at the definition of `⟨▲⟩` we can guess that the
definition should be. A first attempt is:


```agda
⟨△-𝔹²⟩₀ : 𝔹² × 𝔹² → 𝔹²
⟨△-𝔹²⟩₀ ((𝕥 , b) , r₂) = (𝕥 , b)
⟨△-𝔹²⟩₀ ((𝕗 , 𝕗) , r₂) = (𝕗 , 𝕗)
⟨△-𝔹²⟩₀ ((𝕗 , 𝕥) , r₂) = r₂
```

However, closer scrutiny yields this more succinct definition

```agda
⟨△-𝔹²⟩ : 𝔹² × 𝔹² → 𝔹²
⟨△-𝔹²⟩ ((𝕗 , 𝕥) , r₂) = r₂
⟨△-𝔹²⟩ (r₁    ,  r₂) = r₁
```

This translates to a categorical representation as follows:

```agda
⟨△-𝔹̂²⟩ : 𝔹̂² × 𝔹̂² ⇨ 𝔹̂²
⟨△-𝔹̂²⟩ = cond ∘ ( (⟨∧⟩ ∘ (first not) ∘ exl) ▵ exl ▵ exr)


⟨△-𝔹̂²⟩≗⟨△-𝔹²⟩ : Fₘ ⟨△-𝔹̂²⟩ ≗ ⟨△-𝔹²⟩
⟨△-𝔹̂²⟩≗⟨△-𝔹²⟩ =
  λ { ((𝕗 , 𝕗) , _) →  refl
    ; ((𝕗 , 𝕥) , _) →  refl
    ; ((𝕥 , 𝕗) , _) →  refl
    ; ((𝕥 , 𝕥) , _) →  refl
    }
```

We can also show that it's a refinement of `⟨▲⟩`, and a monoid operator.

```agda
⟨△-𝔹̂²⟩-is-⟨▲⟩-refinement : is-⟨▲⟩-refinement 𝔹²-to-R (Fₘ ⟨△-𝔹̂²⟩)
⟨△-𝔹̂²⟩-is-⟨▲⟩-refinement =
  λ { ((𝕗 , 𝕗) , _) → refl
    ; ((𝕗 , 𝕥) , _) → refl
    ; ((𝕥 , _) , _) → refl
    }
```

## A combinator for the `𝔹³` representation of `R`

A first attempt at the monoid operator is achieved by some simple
equational reasoning on the definition of `⟨▲⟩`.

```agda
⟨△-𝔹³⟩₀ : 𝔹³ × 𝔹³ → 𝔹³
⟨△-𝔹³⟩₀ (v@(𝕥 , _ , _) , r₂) = v
⟨△-𝔹³⟩₀ (  (𝕗 , 𝕥 , _) , r₂) = r₂
⟨△-𝔹³⟩₀ (v@(𝕗 , 𝕗 , 𝕥) , r₂) = v
⟨△-𝔹³⟩₀ (v@(𝕗 , 𝕗 , 𝕗) , r₂) = v
```

However, it quickly becomes clear that the following definition is
equivalent.

```agda
⟨△-𝔹³⟩ : 𝔹³ × 𝔹³ → 𝔹³
⟨△-𝔹³⟩ (  (𝕗 , 𝕥 , _) , r₂) = r₂
⟨△-𝔹³⟩ (  r₁         , r₂) = r₁
```

The translation to a categorical representation is straightforward.

```agda
⟨△-𝔹̂³⟩ : 𝔹̂³ × 𝔹̂³ ⇨ 𝔹̂³
⟨△-𝔹̂³⟩ = cond ∘ ((⟨∧⟩ ∘ ((not ∘ e₁) ▵ e₂)) ▵ exl ▵ exr)
  where
    e₁ e₂ : 𝔹̂³ × 𝔹̂³ ⇨ 𝔹̂
    e₁ = exl ∘ exl
    e₂ = exl ∘ exr ∘ exl
```

And finally we prove it's a refinement of `⟨▲⟩` and a monoid-operator.

```agda
⟨△-𝔹̂³⟩-is-⟨▲⟩-refinement : is-⟨▲⟩-refinement 𝔹³-to-R (Fₘ ⟨△-𝔹̂³⟩)
⟨△-𝔹̂³⟩-is-⟨▲⟩-refinement =
  λ { ((𝕥 , _ , _) , _) → refl
    ; ((𝕗 , 𝕥 , _) , _) → refl
    ; ((𝕗 , 𝕗 , 𝕥) , _) → refl
    ; ((𝕗 , 𝕗 , 𝕗) , _) → refl
    }
```


```agda
-- 𝔹²-compare : 𝔹² × 𝔹² → 𝔹²
-- 𝔹²-compare = 𝔹-compare-𝔹² ●̂ 𝔹-compare-𝔹²
--   where
--    _●̂_ : ∀ {τₘ τₙ} → D 𝔹² τₘ → D 𝔹² τₙ  → D 𝔹² (τₘ × τₙ)
--    _●̂_ = mk-●̂ opᴮ
```

And now a 4-bit comparison.

```agda
-- 𝔹⁴-compare : (𝔹² × 𝔹²) × (𝔹² × 𝔹²) → 𝔹²
-- 𝔹⁴-compare = (𝔹-compare-𝔹² ●̂ 𝔹-compare-𝔹²) ●̂ (𝔹-compare-𝔹² ●̂ 𝔹-compare-𝔹²)
--  where
--    _●̂_ : ∀ {τₘ τₙ} → D 𝔹² τₘ → D 𝔹² τₙ  → D 𝔹² (τₘ × τₙ)
--    _●̂_ = mk-●̂ opᴮ

```

## The diagrams

```agda
{-
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

-- Fₘ-𝔹⁴-compareᶜC : Fₘ 𝔹⁴-compareC ≡ 𝔹⁴-compare
-- Fₘ-𝔹⁴-compareᶜC  = refl
-}
```

```agda
{-
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
-}
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

```agda
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

```agda
Σ𝔹³ : Set
Σ𝔹³ = Σ 𝔹³ (λ x → hotness x ≡ 1)
```

We can then define the conversion functions to and from `Σ𝔹³`.

```agda
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

```agda
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









-------------------------------------- begin scratch 2

[TODO: Consider using Raw/Lawless representation for ⟨▲⟩ ]

```agda
module homo-monoid-proof {ρ : Set} (ν : ρ → R) (⟨△⟩ : ρ × ρ → ρ) (e : ρ)
    ⦃ e-is= : ν e ≡ is= ⦄
    (is-refine : is-⟨▲⟩-refinement ν ⟨△⟩)
  where

  homo : ∀ x y → ν (⟨△⟩ (x , y)) ≡ ⟨▲⟩ (ν x , ν y)
  homo x y = sym (is-refine (x , y))

  _≈ρ_ : ρ → ρ → Set
  a ≈ρ b = ν a ≡ ν b

  open import Algebra.Core
  open import Algebra.Definitions {A = ρ} _≈ρ_
  open import Algebra.Structures {A = ρ} _≈ρ_
  open import Relation.Binary.Structures {A = ρ} _≈ρ_
  open import Level
  open import Relation.Binary.Bundles

  ≈ρ-isEquivalence : IsEquivalence
  ≈ρ-isEquivalence =
    record
      { refl  = refl
      ; sym   = sym
      ; trans = Relation.Binary.PropositionalEquality.trans
      }

  ≈ρ-setoid : Setoid 0ℓ 0ℓ
  ≈ρ-setoid =
    record
      { Carrier = ρ
      ; _≈_ = _≈ρ_
      ; isEquivalence = ≈ρ-isEquivalence
      }

  _△_ : Op₂ ρ
  _△_ = curry ⟨△⟩

  △-identityˡ : LeftIdentity e _△_
  △-identityˡ x rewrite homo e x | e-is= = _▲_-proofs.▲-identityˡ (ν x)

  △-identityʳ : RightIdentity e _△_
  △-identityʳ x rewrite homo x e | e-is= = _▲_-proofs.▲-identityʳ (ν x)

  △-identity : Identity e _△_
  △-identity =  △-identityˡ , △-identityʳ

  △-assoc : Associative _△_
  △-assoc x y z rewrite homo ((⟨△⟩ (x , y))) z | homo x y |
                        homo x (⟨△⟩ (y , z)) | homo y z =
    _▲_-proofs.▲-assoc (ν x) (ν y) (ν z)

  △-cong : ∀ {x y u v} → x ≈ρ y → u ≈ρ v → (x △ u) ≈ρ (y △ v)
  △-cong {x} {y} {u} {v} x≈ρy u≈ρv rewrite homo x u | x≈ρy | homo y v | u≈ρv = refl

  △-isMagma : IsMagma _△_
  △-isMagma = record { isEquivalence = ≈ρ-isEquivalence; ∙-cong = △-cong  }

  △-isSemigroup : IsSemigroup _△_
  △-isSemigroup = record { isMagma = △-isMagma; assoc = △-assoc }

  △-isMonoid : IsMonoid _△_ e
  △-isMonoid = record { isSemigroup = △-isSemigroup; identity = △-identity }


```

And now to test

```
-- open homo-monoid-proof 𝔹³-to-R (Fₘ ⟨△-𝔹̂³⟩) (𝕗 , 𝕥 , 𝕗) ⟨△-𝔹̂³⟩-is-⟨▲⟩-refinement
open homo-monoid-proof 𝔹²-to-R (Fₘ ⟨△-𝔹̂²⟩) (𝕗 , 𝕥) ⟨△-𝔹̂²⟩-is-⟨▲⟩-refinement

```



-----
