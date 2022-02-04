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

```
module DelaySemiring where

-- introduce HasSemiring ℕ+⁻∞ instance into scope
module _ where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Algebra.Structures {A = ℕ} _≡_
  open import Algebra.Definitions {A = ℕ} _≡_

  instance
    isDistrib : _*_ DistributesOver _+_
    isDistrib = *-distrib-+

    isCommutativeSemigroup : IsCommutativeSemigroup _+_
    isCommutativeSemigroup = +-isCommutativeSemigroup

    isMonoid : IsMonoid _*_ 1
    isMonoid = *-1-isMonoid

  open import SemiringByAddingAnnihilatingZero ℕ renaming (A⁺ to ℕ+⁻∞; A[_] to ℕ[_]) public
```
