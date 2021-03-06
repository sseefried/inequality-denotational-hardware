<!-- -*-agda2-*- -->

## A semiring for Delay Analysis

This module is based on Conal Elliott's work on circuit timing
analysis available
[here](https://github.com/conal/talk-2012-linear-timing#readme)


In this module we construct a _semiring_ that we will use for Delay
Analysis. Delay analaysis is concerned with analysing the delays
between inputs and outputs of a function. The inputs may not all be
evaluated at the same time. Further, not all of the outputs may depend
on all of the inputs being evaluated so it is possible, in principle,
for some outputs to be evaluated before all of the inputs even have.

A diagram will be helpful. Consider the following function with
two inputs and three outputs or, if you like, a function that takes
a pair and evaluates to a triple.

```plain
      ╔═══╗
A ────╢   ╟─── C
      ║ f ╟─── D
B ────╢   ╟─── E
      ╚═══╝
```

A delay analysis of this function will take into account a total of 6
delays: AC, AD, AE, BC, BD, BE.

First we must be clear on what a delay is. A delay is the amount of
time — after an input is evaluated — that it takes for the output to be
evaluated.

The amount of time it takes for the entire function to evaluate or
simply, the delay of the function, is the maximum of all the delays
between the inputs and outputs. In our example it would be the maximum
of the 6 delays mentioned above.

This is not particularly interesting or useful. The utility of delay
analysis comes when we consider _function composition_. By playing
with different examples we can quickly convince ourselves that the
maximum delay of a composed function can be less than the sum of the
maximum delays of the two functions. For example consider the
composition below:


```plain
      ╔═══╗     ╔═══╗
      ║   ╟──B──║   ║
  A ──╢ f ║     ║ g ╟── D
      ║   ╟──C──║   ║
      ╚═══╝     ╚═══╝
```

Now we must define how delays are composed when functions are
composed. For the sake of intuition, I will avoid generalising too
early and simply walk the reader through the example above.

Function `f` has delays `AB` and `AC` while function `g` has delays
`BD` and `CD`. The composition of these two functions, `g
∘ f` has only one delay: `AD`. How do we calculate this
delay? In general there are two cases to consider. When:

1. an output of one function becomes the input of another
2. there are multiple paths from an input of `f` to an output of `g`

In case 1 we simply add the delays. In case 2 we take the maximum of
two paths.

In this particular example output `B` and `C` of function `f` become
the inputs to function `g` and there are two distinct paths from `A`
to `D`. They are `AB ⟶ BD` and `AC ⟶ CD` respectively.

In this particular example our delay `AD` is equal to `max (AB + BD,
AC + AD)`.  If function `g` has delays `AB = 1`, `AC = 2` and function
`f` has delays `BD = 2` and `CD = 1 then we would get `AD = 3`.

However, if we were to sum the maximum delays of function `f` and `g`
we would get `4`. The difference in these delay values makes it clear
why considering the delays between individual inputs and outputs is
necessary.

[TODO: Perhaps provide a general definition now?]

While the composition of delays of functions forms the heart of Delay
Analysis it is not the full story. A key part of the definition of
_delay_ is the phrase "after an input is evaluated". It is quite
possible that an input is a constant, in which case there was never a
time at which it _became_ evaluated; it was _always_ evaluated.

This concept is, admittedly, a little mind bending. There is an
analogy one can use to make better sense of it. It is to consider what
an optimising compiler might do with the expression `1 + 2`, i.e. the
function `_+_` applied to constants `1` and `2`. It is possible to
completely avoid running the `_+_` function and simply replace this
with _another_ constant `3`. Many optimising compilers do just such a
thing via the _constant folding_ optimisation. Further, when they do
so the compiler does not generate any code to do the addition. In a
sense, the output is evaluated before one has even run the program!

Notice that we do not speak of the delay of inputs, only the delay
between input/output pairs. Thus, we can only speak of _constant
functions_, those that ignore their input and always produce the same
output. We introduce a special delay, `­∞`, between the inputs and
outputs of a _constant function_. Further, we define addition of
delays such that `-∞ + a = -∞` for all finite delays `a`.

Through this lens it is clear that the delay of `_+_ 1 2` will
be. Function `_+_` has two inputs, `A` and `B`, and one output, `C`.
For the purposes of this example it doesn't matter what the _finite_
delays `AC` and `BC` are. In this framework we think of `_+_ 1 2` as
the function `_+_` composed with the constant function (of one input)
that produces the outputs `1` and `2`. The single delay of the
resulting composition has value `-∞`.

We can see this by defining the delays `IA = -∞` and `IB = `-∞` and
calculating what the delay `IC`. `IC = max(IA + AC, IB + BC) = max (-∞
+ AC, -∞ + BC) = -∞`.

```agda
module DelaySemiring where

-- introduce HasSemiring ℕ+⁻∞ instance into scope
open import Data.Nat.Properties using (⊔-isCommutativeSemigroup; +-0-isMonoid; +-distrib-⊔)

open import SemiringExtras renaming (A⁺ to ℕ+⁻∞; A[_] to ℕ[_]; 0# to ⁻∞) public

open SemiringByAddingAnnihilatingZero
        ⊔-isCommutativeSemigroup +-0-isMonoid +-distrib-⊔
         public

open import HasAlgebra renaming (_+_ to _⊔_; _*_ to _+_) public

module _ where
  open import Level using (0ℓ)
  open import Relation.Binary.PropositionalEquality using (_≡_; cong)
          renaming (isEquivalence to ≡-isEquivalence; refl to ≡-refl)
  open import Data.Nat using (ℕ) renaming (_≤_ to _≤ᴺ_)
  import Data.Nat.Properties as ℕ

  module _ (A : Set) where
    open import Relation.Binary.Structures (_≡_ {A = A}) public
    open import Relation.Binary.Core public
    open import Relation.Binary.Definitions public
    open import Relation.Binary.Bundles public


  open import Data.Sum
  open IsTotalPreorder ⦃ … ⦄

  instance
    _ : IsTotalPreorder ℕ _≤ᴺ_
    _ = ℕ.≤-isTotalPreorder

  data _≤_ : ℕ+⁻∞ → ℕ+⁻∞ → Set where
    ⁻∞≤n : {n : ℕ+⁻∞} → ⁻∞ ≤ n
    ℕ≤ℕ  : {m n : ℕ} → m ≤ᴺ n → ℕ[ m ] ≤ ℕ[ n ]

  _≥_ : ℕ+⁻∞ → ℕ+⁻∞ → Set
  a ≥ b = b ≤ a

  ≤-isPreorder : IsPreorder ℕ+⁻∞ _≤_
  ≤-isPreorder =
    record
      { isEquivalence = ≡-isEquivalence
      ; reflexive = λ { {⁻∞} ≡-refl → ⁻∞≤n ; {ℕ[ _ ]} ≡-refl → ℕ≤ℕ (reflexive ℕ ≡-refl) }
      ; trans = λ { ⁻∞≤n _ → ⁻∞≤n
                  ; (ℕ≤ℕ m≤ᴬn) (ℕ≤ℕ n≤ᴬp) → ℕ≤ℕ (trans ℕ m≤ᴬn n≤ᴬp)
                  }
      }

  ≤-total : Total _≤_
  ≤-total ⁻∞ _ = inj₁ ⁻∞≤n
  ≤-total _ ⁻∞ = inj₂ ⁻∞≤n
  ≤-total (ℕ[ i ]) (ℕ[ j ]) = map ℕ≤ℕ ℕ≤ℕ (total i j)

  ≤-isTotalPreorder : IsTotalPreorder ℕ+⁻∞ _≤_
  ≤-isTotalPreorder = record
    { isPreorder = ≤-isPreorder
    ; total = ≤-total
    }

  ≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
  ≤-totalPreorder =
    record
      { Carrier = ℕ+⁻∞
      ; _≈_     = _≡_
      ; _≲_     = _≤_
      ; isTotalPreorder = ≤-isTotalPreorder
      }

  ≤-isPartialOrder : IsPartialOrder ℕ+⁻∞ _≤_
  ≤-isPartialOrder =
    record
      { isPreorder = ≤-isPreorder
      ; antisym    = λ { ⁻∞≤n ⁻∞≤n → ≡-refl ; (ℕ≤ℕ i≤j) (ℕ≤ℕ j≤i) → cong ℕ[_] (ℕ.≤-antisym i≤j j≤i) }
      }

  ≤-poset : Poset 0ℓ 0ℓ 0ℓ
  ≤-poset =
    record
      { Carrier = ℕ+⁻∞
      ; _≈_ = _≡_
      ; _≤_ = _≤_
      ; isPartialOrder = ≤-isPartialOrder }

  import Algebra.Construct.NaturalChoice.MaxOp ℕ.⊔-operator as ℕ-MaxOp
  open import Algebra.Construct.NaturalChoice.Base using (MaxOperator)

  i≤j⇒i⊔j≡j : {i j : ℕ+⁻∞} → i ≤ j → i ⊔ j ≡ j
  i≤j⇒i⊔j≡j ⁻∞≤n       = ≡-refl
  i≤j⇒i⊔j≡j (ℕ≤ℕ x≤y)  = cong ℕ[_] (MaxOperator.x≤y⇒x⊔y≈y ℕ.⊔-operator x≤y)

  i≥j⇒i⊔j≡i : {i j : ℕ+⁻∞} → i ≥ j → i ⊔ j ≡ i
  i≥j⇒i⊔j≡i {i} {j} i≤j rewrite +-comm {x = i} {j} = i≤j⇒i⊔j≡j {j} {i} i≤j

  ⊔-operator : MaxOperator ≤-totalPreorder
  ⊔-operator = record
    { _⊔_ = _⊔_
    ; x≤y⇒x⊔y≈y = i≤j⇒i⊔j≡j
    ; x≥y⇒x⊔y≈x = i≥j⇒i⊔j≡i
    }

  open import Algebra.Construct.NaturalChoice.MaxOp ⊔-operator public

  +-monoʳ-≤ : ∀ n → (_+_ n) Preserves _≤_ ⟶ _≤_
  +-monoʳ-≤ ⁻∞ _ = ⁻∞≤n
  +-monoʳ-≤ ℕ[ m ] ⁻∞≤n  = ⁻∞≤n
  +-monoʳ-≤ ℕ[ m ] (ℕ≤ℕ x≤y) = ℕ≤ℕ (ℕ.+-monoʳ-≤ m x≤y)

--
-- Examples
--

module private-examples where
  open import Relation.Binary.PropositionalEquality
  open import Level using (0ℓ)

  ex1 : ∀ n → n ⊔ ⁻∞ ≡ ℕ[ 0 ] + n
  ex1 n =
      begin
        n ⊔ ⁻∞       ≡⟨ HasAlgebra.+-identityʳ ⟩
        n            ≡⟨ sym (HasAlgebra.*-identityˡ) ⟩
        ℕ[ 0 ] + n
      ∎
    where open ≡-Reasoning

  ex2 : ∀ n → n + ℕ[ 0 ] ≡ n
  ex2 n = HasAlgebra.*-identityʳ {x = n}
```
