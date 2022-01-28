module OrderingMonoid where

import Level as L
open import Data.Bool
open import Data.Nat hiding (_⊔_;_+_)
open import Data.Nat.Properties
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Categorical.Raw
open import Categorical.Equiv hiding (refl)
open import Functions hiding (tt ; if_then_else_)
open import Data.Unit renaming (⊤ to Unit)
import Categorical.Laws as Laws
open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; _,_) renaming (_×_ to _×′_)
open import Relation.Nullary

open import Level using (Level; Lift; Setω; 0ℓ) renaming (suc to lsuc)

private variable
  o : Level
  obj : Set o

record RRep {o : Level} (obj : Set o) : Set (lsuc o) where
  field
    ⋚ : obj

open RRep ⦃ … ⦄ public

record RMonoid {o ℓ : Level} {obj : Set o} ⦃ products : Products obj ⦄ ⦃ rrep : RRep obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o L.⊔ ℓ) where

  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    is< : ⊤ ⇨ ⋚
    is> : ⊤ ⇨ ⋚
    is= : ⊤ ⇨ ⋚
    ⟨△⟩ : ⋚ × ⋚ ⇨ ⋚

open RMonoid ⦃ … ⦄ public

infixr 2 _`×_
data Ty : Set where
  `⊤    : Ty
  `⋚    : Ty
  _`×_  : Ty → Ty → Ty

expr : Setω
expr = ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : RRep obj ⦄ ⦃ _ : RMonoid _⇨_ ⦄ → ⊤ ⇨ ⋚

ex0 : expr
ex0 = is<

ex1 : expr
ex1 = ⟨△⟩ ∘ (is<  ▵ is= )

ex2 : expr
ex2 = ⟨△⟩ ∘ (⟨△⟩ ∘ (is<  ▵ is= ) ▵ ⟨△⟩ ∘ (is>  ▵ is< ))

ex3 : expr
ex3 = ⟨△⟩ ∘ (bigger ▵ smaller)
  where
    bigger = ⟨△⟩ ∘ (⟨△⟩ ∘ (is<  ▵ is= ) ▵ ⟨△⟩ ∘ (is>  ▵ is< ))
    smaller = ⟨△⟩ ∘ (is<  ▵ is= )

ex4 : expr
ex4 {_} {_} {_⇨_} = step3
  where
    step1a step1b step1c step1d step2a step2b step3 : ⊤ ⇨ ⋚
    step1a = ⟨△⟩ ∘ (is<  ▵ is= )
    step1b = ⟨△⟩ ∘ (is>  ▵ is= )
    step1c = ⟨△⟩ ∘ (is=  ▵ is> )
    step1d = ⟨△⟩ ∘ (is<  ▵ is< )
    step2a = ⟨△⟩ ∘ (step1a  ▵ step1b )
    step2b = ⟨△⟩ ∘ (step1c  ▵ step1d )
    step3  = ⟨△⟩ ∘ (step2a  ▵ step2b )

ex5 : expr
ex5 = ⟨△⟩ ∘ (is< ▵ (⟨△⟩ ∘ (is= ▵ (⟨△⟩ ∘ (is> ▵ (⟨△⟩ ∘ (is= ▵ (⟨△⟩ ∘ (is= ▵ (⟨△⟩ ∘ (is> ▵ (⟨△⟩ ∘ (is< ▵ is<)))))))))))))


ex6 ex7 : ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : RRep obj ⦄ ⦃ _ : RMonoid _⇨_ ⦄ → (((⋚ × ⋚) × (⋚ × ⋚)) × ((⋚ × ⋚) × (⋚ × ⋚))) ⇨ ⋚
ex6 {_} {_} {_⇨_} = step3
  where
    x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : (((⋚ × ⋚) × (⋚ × ⋚)) × ((⋚ × ⋚) × (⋚ × ⋚))) ⇨ ⋚
    x₀ = exl ∘ exl ∘ exl
    x₁ = exr ∘ exl ∘ exl
    x₂ = exl ∘ exr ∘ exl
    x₃ = exr ∘ exr ∘ exl
    x₄ = exl ∘ exl ∘ exr
    x₅ = exr ∘ exl ∘ exr
    x₆ = exl ∘ exr ∘ exr
    x₇ = exr ∘ exr ∘ exr

    step1a step1b step1c step1d step2a step2b step3 : (((⋚ × ⋚) × (⋚ × ⋚)) × ((⋚ × ⋚) × (⋚ × ⋚))) ⇨ ⋚
    step1a = ⟨△⟩ ∘ (x₀  ▵ x₁ )
    step1b = ⟨△⟩ ∘ (x₂  ▵ x₃ )
    step1c = ⟨△⟩ ∘ (x₄  ▵ x₅ )
    step1d = ⟨△⟩ ∘ (x₆  ▵ x₇ )
    step2a = ⟨△⟩ ∘ (step1a  ▵ step1b )
    step2b = ⟨△⟩ ∘ (step1c  ▵ step1d )
    step3  = ⟨△⟩ ∘ (step2a  ▵ step2b )

ex7 {_} {_} {_⇨_} = ⟨△⟩ ∘ (x₀ ▵ (⟨△⟩ ∘ (x₁ ▵ (⟨△⟩ ∘ (x₂ ▵ (⟨△⟩ ∘ (x₃ ▵ (⟨△⟩ ∘ (x₄ ▵ (⟨△⟩ ∘ (x₅ ▵ (⟨△⟩ ∘ (x₆ ▵ x₇)))))))))))))
  where
    x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : (((⋚ × ⋚) × (⋚ × ⋚)) × ((⋚ × ⋚) × (⋚ × ⋚))) ⇨ ⋚
    x₀ = exl ∘ exl ∘ exl
    x₁ = exr ∘ exl ∘ exl
    x₂ = exl ∘ exr ∘ exl
    x₃ = exr ∘ exr ∘ exl
    x₄ = exl ∘ exl ∘ exr
    x₅ = exr ∘ exl ∘ exr
    x₆ = exl ∘ exr ∘ exr
    x₇ = exr ∘ exr ∘ exr

expr2 : Setω
expr2 = ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : RRep obj ⦄ ⦃ _ : RMonoid _⇨_ ⦄ → ((⋚ × ⋚) × (⋚ × ⋚)) ⇨ (⋚ × ⋚)

d₀ : expr2
d₀ = ((⟨△⟩ ⊗ id) ∘ (id ⊗ ⟨△⟩))

d₁ : expr2
d₁ = ((⟨△⟩ ∘ id) ⊗ (id ∘ ⟨△⟩))

_⇨ᶜ_ : Unit → Unit → Set
tt ⇨ᶜ tt = ℕ

max : ℕ → ℕ → ℕ
max x y = if x <ᵇ y then y else x

module Attempt1 where

  instance
    _ : Category  _⇨ᶜ_
    _ = record { id = 0 ; _∘_ = ℕ._+_ } -- "a monoid is a category with one object"
    -- justification : add costs when you compose operations

    _ : Equivalent 0ℓ _⇨ᶜ_
    _ = record { _≈_ = _≡_ ; equiv = isEquivalence }

    _ : Laws.Category  _⇨ᶜ_
    _ = record { identityˡ = refl ; identityʳ = λ {_ _ f} → +-identityʳ f ; assoc = λ {_ _ _ _ f g h}  → +-assoc h g f   ; ∘≈ = cong₂ ℕ._+_ }

    _ : Products Unit
    _ = record { ⊤ = tt ; _×_ = λ _ _ → tt }

    _ : Cartesian _⇨ᶜ_
    _ = record { ! = 0 ; _▵_ = max ; exl = 0 ; exr = 0 }
    -- Justification: decomposing (exl, exr) takes zero work. forking (_▵_) is the maximum work in the two branches.

    why-∀⊤-aint-true : {a b c d : Unit} → Σ (a ⇨ᶜ b) (λ a₁ → Σ (c ⇨ᶜ d) (λ a₂ → ¬ (a₁ ≈ a₂)))
    why-∀⊤-aint-true = (0 , 1 , λ ())

--    _ : Laws.Cartesian _⇨ᶜ_ can't be proved

    _ : RRep Unit
    _ = record { ⋚ = tt }

    _ : RMonoid _⇨ᶜ_
    _ = record { is< = 0 ; is> = 0 ; is= = 0 ; ⟨△⟩ = 1 }
    -- Justification: Applying ⟨△⟩ costs one unit of work. Everything else is zero

  ex0′ ex1′ ex2′ ex3′ ex4′ ex5′ d₀′ d₁′ : ℕ
  ex0′ = ex0 -- cost = 0
  ex1′ = ex1 -- cost = 1
  ex2′ = ex2 -- cost = 2
  ex3′ = ex3 -- cost = 3
  ex4′ = ex4 -- cost = 3
  ex5′ = ex5 -- cost = 7
  d₀′ = d₀
  d₁′ = d₁

  _ : Set
  _ = {! d₁′ !}

module Attempt2 where
  open import Data.Vec
  import Data.Vec as V
  open import Data.Integer hiding (_+_)
  import Data.Integer as ℤ
  import Data.Sign as S
  open Data.Product renaming  (_×_ to _×′)
  open import Function hiding (id)

  Matrix : Set → ℕ → ℕ → Set
  Matrix A m n =  Vec (Vec A n) m


  data ℤ∞ : Set where
    -∞   : ℤ∞
    finℤ : ℤ → ℤ∞

  #1 : ℤ∞
  #1 = finℤ 0ℤ

  #0 : ℤ∞
  #0 = -∞

  _+_ : ℤ∞ → ℤ∞ → ℤ∞
  -∞ + _  = -∞
  _  + -∞ = -∞
  (finℤ m) + (finℤ n) = finℤ (m ℤ.+ n)

  ℤ∞-max : ℤ∞ → ℤ∞ → ℤ∞
  ℤ∞-max -∞ b = b
  ℤ∞-max a -∞ = a
  ℤ∞-max (finℤ m) (finℤ n) = finℤ (m ℤ.⊔ n)

  _∙_ : {n : ℕ} → Vec ℤ∞ n → Vec ℤ∞ n → ℤ∞
  _∙_ {n} v₁ v₂ = foldl _ ℤ∞-max #0 (zipWith _+_ v₁ v₂)

  -- objects are ℤ
  -- morphisms are matrices
  -- composition is matrix multiplication

  cross : ∀ {A} {m n : ℕ} → Vec A m → Vec A n → Matrix (A ×′ A) m n
  cross {m = zero} _ _ = []
  cross {m = suc m} (x₁ ∷ x₁s) x₂s =  (V.map (λ x₂ → (x₁ , x₂)) x₂s) ∷ cross x₁s x₂s

  identityMatrix : {n : ℕ} → Matrix ℤ∞ n n
  identityMatrix = V.map 1-in-pos indices
    where
      1-in-pos : {n : ℕ} → ℕ → Vec ℤ∞ n
      1-in-pos {zero} _ = []
      1-in-pos {suc n} m with m ℕ.≟ n
      ... | yes refl = #1 ∷ 1-in-pos m
      ... | no _     = #0 ∷ 1-in-pos m

      indices : {n : ℕ} → Vec ℕ n
      indices {zero}  = []
      indices {suc n} = n ∷ indices {n}

  _∗_ : {m n p : ℕ} → Matrix ℤ∞ m n → Matrix ℤ∞ n p → Matrix ℤ∞ m p
  [] ∗ _ = []
  _∗_ {suc m} (v₁ ∷ m₁) m₂ = V.map (λ v₂ → v₁ ∙ v₂) (V.transpose m₂) ∷ m₁ ∗ m₂

  _⇨_ : ℕ → ℕ → Set
  c ⇨ r = Matrix ℤ∞ r c

  zeroMatrix : {m n : ℕ} → Matrix ℤ∞ m n
  zeroMatrix = replicate (replicate #0)

  [[-∞]] : 1 ⇨ 1
  [[-∞]] = zeroMatrix

  [[0]] : 1 ⇨ 1
  [[0]] = identityMatrix

  -- [A | B]
  joinMatrix : {m n p : ℕ} → Matrix ℤ∞ m n → Matrix ℤ∞ m p → Matrix ℤ∞ m (n ℕ.+ p)
  joinMatrix = zipWith V._++_

  instance
    _ : Category {obj = ℕ} _⇨_
    _ = record { id = identityMatrix ; _∘_ = _∗_ }

    _ : Products ℕ
    _ = record { ⊤ = 1 ; _×_ = ℕ._+_ }

    _ : Cartesian {obj = ℕ} _⇨_
    _ = record { !   = replicate #0 ∷ []
               ; _▵_ = V._++_ -- [A]
                              -- [-]
                              -- [B]
               ; exl = joinMatrix identityMatrix zeroMatrix
               ; exr = joinMatrix zeroMatrix identityMatrix
               }
    _ : RRep ℕ
    _ = record { ⋚ = 1 }

    _ : RMonoid _⇨_
    _ = record { is< = [[-∞]]
               ; is> = [[-∞]]
               ; is= = [[-∞]]
               ; ⟨△⟩ = (finℤ 1ℤ ∷ finℤ 1ℤ ∷ []) ∷ []
               }

  ex0′ ex1′ ex2′ ex3′ ex4′ ex5′  : 1 ⇨ 1
  ex0′ = ex0
  ex1′ = ex1
  ex2′ = ex2
  ex3′ = ex3
  ex4′ = ex4
  ex5′ = ex5

  ex6′ ex7′ : 8 ⇨ 1
  ex6′ = ex6
  ex7′ = ex7

  d₀′ d₁′ : 4 ⇨ 2
  d₀′ = d₀
  d₁′ = d₁

  _ : Set
  _ = {! d₀′!}
