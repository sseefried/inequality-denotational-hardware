module RMonoid where

open import Level
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Categorical.Raw
open import Categorical.Equiv hiding (refl)
open import Functions hiding (tt ; if_then_else_)
open import Data.Unit renaming (⊤ to Unit)
import Categorical.Laws as Laws
open import Relation.Binary.PropositionalEquality

private variable
  o : Level
  obj : Set o

open import Level using (Level; _⊔_; Lift) renaming (suc to lsuc)

record RRep {o : Level} (obj : Set o) : Set (lsuc o) where
  field
    R : obj

open RRep ⦃ … ⦄ public

record RMonoid {o ℓ : Level} {obj : Set o} ⦃ products : Products obj ⦄ ⦃ rrep : RRep obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where

  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    is< : ⊤ ⇨ R
    is> : ⊤ ⇨ R
    is= : ⊤ ⇨ R
    ⟨△⟩ : R × R ⇨ R

open RMonoid ⦃ … ⦄ public

infixr 2 _`×_
data Ty : Set where
  `⊤    : Ty
  `R    : Ty
  _`×_  : Ty → Ty → Ty

expr :  Setω
expr = ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : RRep obj ⦄ ⦃ _ : RMonoid _⇨_ ⦄ → ⊤ ⇨ R

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
    step1a step1b step1c step1d step2a step2b step3 : ⊤ ⇨ R
    step1a = ⟨△⟩ ∘ (is<  ▵ is= )
    step1b = ⟨△⟩ ∘ (is>  ▵ is= )
    step1c = ⟨△⟩ ∘ (is=  ▵ is> )
    step1d = ⟨△⟩ ∘ (is<  ▵ is< )
    step2a = ⟨△⟩ ∘ (step1a  ▵ step1b )
    step2b = ⟨△⟩ ∘ (step1c  ▵ step1d )
    step3  = ⟨△⟩ ∘ (step2a  ▵ step2b )

ex5 : expr
ex5 = ⟨△⟩ ∘ (is< ▵ (⟨△⟩ ∘ (is= ▵ (⟨△⟩ ∘ (is> ▵ (⟨△⟩ ∘ (is= ▵ (⟨△⟩ ∘ (is= ▵ (⟨△⟩ ∘ (is> ▵ (⟨△⟩ ∘ (is< ▵ is<)))))))))))))

_⇨ᶜ_ : Unit → Unit → Set
tt ⇨ᶜ tt = ℕ

max : ℕ → ℕ → ℕ
max x y = if x <ᵇ y then y else x

instance
  _ : Category  _⇨ᶜ_
  _ = record { id = 0 ; _∘_ = _+_ } -- "a monoid is a category with one object"
  -- justification : add costs when you compose operations

  _ : Equivalent 0ℓ _⇨ᶜ_
  _ = record { _≈_ = _≡_ ; equiv = isEquivalence }

  _ : Laws.Category  _⇨ᶜ_
  _ = record { identityˡ = refl ; identityʳ = λ {_ _ f} → +-identityʳ f ; assoc = λ {_ _ _ _ f g h}  → +-assoc h g f   ; ∘≈ = cong₂ _+_ }

  _ : Products Unit
  _ = record { ⊤ = tt ; _×_ = λ _ _ → tt }

  _ : Cartesian _⇨ᶜ_
  _ = record { ! = 0 ; _▵_ = max ; exl = 0 ; exr = 0 }
  -- Justification: decomposing (exl, exr) takes zero work. forking (_▵_) is the maximum work in the two branches.

  _ : RRep Unit
  _ = record { R = tt }

  _ : RMonoid _⇨ᶜ_
  _ = record { is< = 0 ; is> = 0 ; is= = 0 ; ⟨△⟩ = 1 }
  -- Justification: Applying ⟨△⟩ costs one unit of work. Everything else is zero

ex0′ ex1′ ex2′ ex3′ ex4′ ex5′ : ℕ
ex0′ = ex0 -- cost = 0
ex1′ = ex1 -- cost = 1
ex2′ = ex2 -- cost = 2
ex3′ = ex3 -- cost = 3
ex4′ = ex4 -- cost = 3
ex5′ = ex5 -- cost = 7

_ : Set
_ = {!ex5′!}
