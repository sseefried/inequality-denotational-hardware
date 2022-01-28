module OrderingMonoid where

import Level as L
open import Data.Bool
open import Data.Nat hiding (_⊔_;_+_;_*_)
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

record ⋚-Rep {o : Level} (obj : Set o) : Set (lsuc o) where
  field
    ⋚ : obj

open ⋚-Rep ⦃ … ⦄ public

record RMonoid {o ℓ : Level} {obj : Set o} ⦃ products : Products obj ⦄ ⦃ rrep : ⋚-Rep obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o L.⊔ ℓ) where

  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    is< : ⊤ ⇨ ⋚
    is> : ⊤ ⇨ ⋚
    is= : ⊤ ⇨ ⋚
    ⟨▲⟩ : ⋚ × ⋚ ⇨ ⋚

open RMonoid ⦃ … ⦄ public

infixr 2 _`×_
data Ty : Set where
  `⊤    : Ty
  `⋚    : Ty
  _`×_  : Ty → Ty → Ty


module Examples where

  expr : Setω
  expr = ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : ⋚-Rep obj ⦄ ⦃ _ : RMonoid _⇨_ ⦄ → ⊤ ⇨ ⋚

  ex0 : expr
  ex0 = is<

  ex1 : expr
  ex1 = ⟨▲⟩ ∘ (is<  ▵ is= )

  ex2 : expr
  ex2 = ⟨▲⟩ ∘ (⟨▲⟩ ∘ (is<  ▵ is= ) ▵ ⟨▲⟩ ∘ (is>  ▵ is< ))

  ex3 : expr
  ex3 = ⟨▲⟩ ∘ (bigger ▵ smaller)
    where
      bigger = ⟨▲⟩ ∘ (⟨▲⟩ ∘ (is<  ▵ is= ) ▵ ⟨▲⟩ ∘ (is>  ▵ is< ))
      smaller = ⟨▲⟩ ∘ (is<  ▵ is= )

  ex4 : expr
  ex4 {_} {_} {_⇨_} = step3
    where
      step1a step1b step1c step1d step2a step2b step3 : ⊤ ⇨ ⋚
      step1a = ⟨▲⟩ ∘ (is<  ▵ is= )
      step1b = ⟨▲⟩ ∘ (is>  ▵ is= )
      step1c = ⟨▲⟩ ∘ (is=  ▵ is> )
      step1d = ⟨▲⟩ ∘ (is<  ▵ is< )
      step2a = ⟨▲⟩ ∘ (step1a  ▵ step1b )
      step2b = ⟨▲⟩ ∘ (step1c  ▵ step1d )
      step3  = ⟨▲⟩ ∘ (step2a  ▵ step2b )

  ex5 : expr
  ex5 = ⟨▲⟩ ∘ (is< ▵ (⟨▲⟩ ∘ (is= ▵ (⟨▲⟩ ∘ (is> ▵ (⟨▲⟩ ∘ (is= ▵ (⟨▲⟩ ∘ (is= ▵ (⟨▲⟩ ∘ (is> ▵ (⟨▲⟩ ∘ (is< ▵ is<)))))))))))))


  ex6 ex7 : ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : ⋚-Rep obj ⦄ ⦃ _ : RMonoid _⇨_ ⦄ → (((⋚ × ⋚) × (⋚ × ⋚)) × ((⋚ × ⋚) × (⋚ × ⋚))) ⇨ ⋚
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
      step1a = ⟨▲⟩ ∘ (x₀  ▵ x₁ )
      step1b = ⟨▲⟩ ∘ (x₂  ▵ x₃ )
      step1c = ⟨▲⟩ ∘ (x₄  ▵ x₅ )
      step1d = ⟨▲⟩ ∘ (x₆  ▵ x₇ )
      step2a = ⟨▲⟩ ∘ (step1a  ▵ step1b )
      step2b = ⟨▲⟩ ∘ (step1c  ▵ step1d )
      step3  = ⟨▲⟩ ∘ (step2a  ▵ step2b )

  ex7 {_} {_} {_⇨_} = ⟨▲⟩ ∘ (x₀ ▵ (⟨▲⟩ ∘ (x₁ ▵ (⟨▲⟩ ∘ (x₂ ▵ (⟨▲⟩ ∘ (x₃ ▵ (⟨▲⟩ ∘ (x₄ ▵ (⟨▲⟩ ∘ (x₅ ▵ (⟨▲⟩ ∘ (x₆ ▵ x₇)))))))))))))
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
  expr2 = ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : ⋚-Rep obj ⦄ ⦃ _ : RMonoid _⇨_ ⦄ → ((⋚ × ⋚) × (⋚ × ⋚)) ⇨ (⋚ × ⋚)

  d₀ : expr2
  d₀ = ((⟨▲⟩ ⊗ id) ∘ (id ⊗ ⟨▲⟩))

  d₁ : expr2
  d₁ = ((⟨▲⟩ ∘ id) ⊗ (id ∘ ⟨▲⟩))


open import Data.Integer hiding (_+_; _*_)
import Data.Integer as ℤ
import Data.Sign as S

data ℤ∞ : Set where
  -∞   : ℤ∞
  finℤ : ℤ → ℤ∞

open import Algebra.Bundles using (RawSemiring)

ℤ∞-Semiring : RawSemiring 0ℓ 0ℓ
ℤ∞-Semiring =
  record
    { Carrier = ℤ∞
    ; _≈_ = _≡_
    ; _+_ = ℤ∞-max
    ; _*_ = _+_
    ; 0# = -∞
    ; 1# = finℤ 0ℤ
    }
  where
    _+_ : ℤ∞ → ℤ∞ → ℤ∞
    -∞ + _  = -∞
    _  + -∞ = -∞
    (finℤ m) + (finℤ n) = finℤ (m ℤ.+ n)

    ℤ∞-max : ℤ∞ → ℤ∞ → ℤ∞
    ℤ∞-max -∞ b = b
    ℤ∞-max a -∞ = a
    ℤ∞-max (finℤ m) (finℤ n) = finℤ (m ℤ.⊔ n)

open import Matrix ℤ∞-Semiring

_⇨_ : ℕ → ℕ → Set
c ⇨ r = Matrix r c

[[-∞]] : 1 ⇨ 1
[[-∞]] = allZero

instance
  _ : Category {obj = ℕ} _⇨_
  _ = record { id = identity ; _∘_ = _∙_ }

  _ : Products ℕ
  _ = record { ⊤ = 1 ; _×_ = ℕ._+_ }

  _ : Cartesian {obj = ℕ} _⇨_
  _ = record { !   = zeroColumn
             ; _▵_ = _↕_
             ; exl = identity ↔ allZero
             ; exr = allZero  ↔ identity
             }
  _ : ⋚-Rep ℕ
  _ = record { ⋚ = 1 }

  _ : RMonoid _⇨_
  _ = record { is< = [[-∞]]
             ; is> = [[-∞]]
             ; is= = [[-∞]]
             ; ⟨▲⟩ = columnOf (finℤ 1ℤ)
             }

module Examples′ where
  open Examples

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


--
-- Perfect trees
--

data PT (A : Set) : ℕ → Set where
   nil  : PT A 0
   leaf : A → PT A 0
   fork : {n : ℕ} → A ×′ PT A n ×′ PT A n → PT A (ℕ.suc n)


pt1 : PT ℕ 0
pt1 = leaf 1

--
--      1
--    2   3
--  4  5  . .

pt5 : PT ℕ 2
pt5 = fork (1 , fork (2 , leaf 4 , leaf 5) , fork (3 , nil , nil))


--
--      1
--    2   3
--  4  5  6 .
pt6 : PT ℕ 2
pt6 = fork (1 , fork (2 , leaf 4 , leaf 5) , fork (3 , leaf 6 , nil))

--
--      1
--    2   3
--  4  5  6 7
pt7 : PT ℕ 2
pt7 = fork (1 , fork (2 , leaf 4 , leaf 5) , fork (3 , leaf 6 , leaf 7))


--
--        1
--    2      3
--  4   5   6   7
-- 8 . . . . . . .
pt8 : PT ℕ 3
pt8 = fork (1 , fork (2 , fork (4 , leaf 8 , nil) , fork (5 , nil , nil))
              , fork (3 , fork (6 , nil    , nil) , fork (7 , nil , nil)))

--
-- Now a function to map an arbitrary length list to a Perfect Tree
--

import Data.Bin as Bin
open import Data.Vec

⌊log₂_⌋ : ℕ → ℕ
⌊log₂ n ⌋  = lg (fromℕ n)
  where
    open Bin
    lg : Bin → ℕ
    lg 0# = 0
    lg  (b⁺ 1#) = Bin.⌊log₂ b⁺ ⌋

_ : ℕ
_ = {!⌊log₂ 1 ⌋!}

--data P : Set where
--  P1 : {n : ℕ} → n ≡ ⌊ n /2⌋ ℕ.+ ⌊ n /2⌋
--  P2 : {n : ℕ} → n ≡ ⌊ n /2⌋ ℕ.+ ⌊ n /2⌋ + 1


--splitHalf : {A : Set} {n : ℕ} → Vec A (ℕ.suc n) → Vec A ⌊ n /2⌋ ×′ Vec A ⌊ n /2⌋
--splitHalf (a ∷ []) = [] , []
--splitHalf (a ∷ as) =

toPT : {A : Set} {n : ℕ} → Vec A n → PT A ⌊log₂ n ⌋
toPT []       =  nil
toPT (a ∷ []) = leaf a
toPT {n = suc (suc  n)} (a ∷ as) =
  let (as₁ , as₂) = split as
  in fork (a , ? , ? )

{-

  1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []
⇒ fork (1 , (toPT  2 ∷ 3 ∷ 4 ∷ []) , (toPT  5 ∷ 6 ∷ 7 ∷ []))
⇒ fork (1 , fork (2 , (toPT  3 ∷ []) (toPt 4 ∷ [])) , fork (5 , toPT 6 ∷ []) , toPT (7 ∷ []))

  1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
⇒ fork (1 , (toPT  2 ∷ 3 ∷ []) , (toPT  4 ∷ 5 ∷ []))
⇒ fork (1 , fork (2 , (toPT  3 ∷ []) (toPt [])) , fork (4 , toPT 5 ∷ []) , toPT [])
⇒ fork (1 , fork (2 , leaf 3 , nil ) , fork (4 , leaf 5 , nil))



-}
