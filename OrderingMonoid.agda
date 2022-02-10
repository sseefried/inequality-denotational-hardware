module OrderingMonoid where

import Level as L
open import Data.Bool hiding (_≤_)
open import Data.Nat hiding (_⊔_;_+_;_*_;_≤_;_≥_; suc)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Categorical.Raw
open import Categorical.Equiv hiding (refl)
open import Functions hiding (tt ; if_then_else_)
open import Data.Unit renaming (⊤ to Unit) hiding (_≤_)
import Categorical.Laws as Laws
open import Relation.Binary.PropositionalEquality renaming (sym to ≡-sym)
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

record ⋚-Monoid {o ℓ : Level} {obj : Set o} ⦃ products : Products obj ⦄ ⦃ rrep : ⋚-Rep obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o L.⊔ ℓ) where

  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    is< : ⊤ ⇨ ⋚
    is> : ⊤ ⇨ ⋚
    is= : ⊤ ⇨ ⋚
    ⟨▲⟩ : ⋚ × ⋚ ⇨ ⋚

open ⋚-Monoid ⦃ … ⦄ public

infixr 2 _`×_
data Ty : Set where
  `⊤    : Ty
  `⋚    : Ty
  _`×_  : Ty → Ty → Ty


module Examples where

  expr : Setω
  expr = ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : ⋚-Rep obj ⦄ ⦃ _ : ⋚-Monoid _⇨_ ⦄ → ⊤ ⇨ ⋚

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


  ex6 ex7 : ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : ⋚-Rep obj ⦄ ⦃ _ : ⋚-Monoid _⇨_ ⦄ → (((⋚ × ⋚) × (⋚ × ⋚)) × ((⋚ × ⋚) × (⋚ × ⋚))) ⇨ ⋚
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
  expr2 = ∀ {o : Level} {obj : Set o} {_⇨_ : obj → obj → Set o} → ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : ⋚-Rep obj ⦄ ⦃ _ : ⋚-Monoid _⇨_ ⦄ → ((⋚ × ⋚) × (⋚ × ⋚)) ⇨ (⋚ × ⋚)

  d₀ : expr2
  d₀ = ((⟨▲⟩ ⊗ id) ∘ (id ⊗ ⟨▲⟩))

  d₁ : expr2
  d₁ = ((⟨▲⟩ ∘ id) ⊗ (id ∘ ⟨▲⟩))


open import DelaySemiring hiding (_∙_)
open import Algebra.Bundles using (RawSemiring)

ℕ+⁻∞-Semiring : RawSemiring 0ℓ 0ℓ
ℕ+⁻∞-Semiring =
  record
    { Carrier = ℕ+⁻∞
    ; _≈_ = _≡_
    ; _+_ = _⊔_
    ; _*_ = _+_
    ; 0# = ⁻∞
    ; 1# = ℕ[ 0 ]
    }

open import Matrix ℕ+⁻∞-Semiring

_⇨_ : ℕ → ℕ → Set
c ⇨ r = Matrix r c

[[⁻∞]] : 1 ⇨ 1
[[⁻∞]] = allZero

instance
  _ : Category {obj = ℕ} _⇨_
  _ = record { id = identity ; _∘_ = _∙_ }

  _ : Products ℕ
  _ = record { ⊤ = 1 ; _×_ = ℕ._+_ }

  _ : Cartesian {obj = ℕ} _⇨_
  _ = record { !   = zeroRow
             ; _▵_ = _↔_
             ; exl = identity ↕ allZero
             ; exr = allZero  ↕ identity
             }
  _ : ⋚-Rep ℕ
  _ = record { ⋚ = 1 }

  _ : ⋚-Monoid _⇨_
  _ = record { is< = [[⁻∞]]
             ; is> = [[⁻∞]]
             ; is= = [[⁻∞]]
             ; ⟨▲⟩ = rowOf (ℕ[ 1 ])
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

--  _ : Set
--  _ = {! ex6′!}


--
-- Perfect trees
--

data PT (A : Set) : ℕ → Set where
   nil  : PT A 0
   leaf : A → PT A 0
   fork : {n : ℕ} → PT A n ×′ PT A n → PT A (ℕ.suc n)


--
--      .
--    .   .
--  1  2  3 .

pt3 : PT ℕ 2
pt3 = fork (fork (leaf 1 , leaf 2) , fork ( leaf 3 , nil))


--          .
--       .    .
--    .     .    .
--  1  2  3  4  5
pt5 : PT ℕ 3
pt5 = fork ( fork (fork (leaf 1 , leaf 2) , fork (leaf 3 , leaf 4))
           , fork (fork (leaf 5 , nil   ) , fork (nil , nil)))



{-

  1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []
⇒ fork (1 , (toPT  2 ∷ 3 ∷ 4 ∷ []) , (toPT  5 ∷ 6 ∷ 7 ∷ []))
⇒ fork (1 , fork (2 , (toPT  3 ∷ []) (toPt 4 ∷ [])) , fork (5 , toPT 6 ∷ []) , toPT (7 ∷ []))
p
  1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
⇒ fork (1 , (toPT  2 ∷ 3 ∷ []) , (toPT  4 ∷ 5 ∷ []))
⇒ fork (1 , fork (2 , (toPT  3 ∷ []) (toPt [])) , fork (4 , toPT 5 ∷ []) , toPT [])
⇒ fork (1 , fork (2 , leaf 3 , nil ) , fork (4 , leaf 5 , nil))



-}

open import Data.Vec


maxMat : {m n : ℕ} → Matrix m n → ℕ+⁻∞
maxMat m = vecMax (map vecMax m)
  where
    vecMax : {n : ℕ} → Vec ℕ+⁻∞ n → ℕ+⁻∞
    vecMax = foldr _ _⊔_ ⁻∞

extract : (1 ⇨ 1) → ℕ+⁻∞
extract ((a ∷ []) ∷ []) = a

data T1 : Set where
  mkT1 : T1

combine : {n : ℕ} → PT T1 n → (1 ⇨ 1)
combine nil                = [[⁻∞]]
combine (leaf _)           = rowOf (ℕ[ 0 ])
combine (fork (pt₁ , pt₂)) = ⟨▲⟩ ∘ (combine pt₁ ▵ combine pt₂)

----

⊔-vec : {n : ℕ} → Vec ℕ+⁻∞ n → ℕ+⁻∞
⊔-vec = foldr _ _⊔_ ⁻∞

dot-⊔ : {n : ℕ} (z : ℕ+⁻∞) (v : Vec ℕ+⁻∞ n) → replicate z · v ≡ z + ⊔-vec v
dot-⊔ ⁻∞       []  = refl
dot-⊔ (ℕ[ _ ]) []  = refl
dot-⊔ {n = ℕ.suc n} z (a ∷ as) =
    begin
      replicate z · (a ∷ as)
    ≡⟨⟩
      (z ∷ replicate z) · (a ∷ as)
    ≡⟨⟩
      foldr _ _⊔_ ⁻∞ (zipWith _+_ (z ∷ replicate z) (a ∷ as))
    ≡⟨⟩
      foldr _ _⊔_ ⁻∞ (z + a ∷ zipWith _+_ (replicate z) as)
    ≡⟨⟩
      (z + a) ⊔ foldr _ _⊔_ ⁻∞ (zipWith _+_ (replicate z) as)
    ≡⟨⟩
      (z + a) ⊔ (replicate z · as)
    ≡⟨ cong ((z + a) ⊔_) (dot-⊔ {n} z as) ⟩
      (z + a) ⊔ (z + ⊔-vec as) -- (z * a) + (z * ⊔-vec as)
    ≡⟨ ≡-sym (*-distribʳ {x = z} {a}) ⟩
      z + (a ⊔ ⊔-vec as)
    ≡⟨⟩
      z + (a ⊔ foldr _ _⊔_ ⁻∞ as)
    ≡⟨⟩
      z + (foldr _ _⊔_ ⁻∞ (a ∷ as))
    ≡⟨⟩
      z + (⊔-vec (a ∷ as))
    ∎
  where
    open ≡-Reasoning

----

+-monoʳ-≤ : ∀ n → (_+_ n) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ ⁻∞ _ = ⁻∞≤n
+-monoʳ-≤ ℕ[ m ] ⁻∞≤n  = ⁻∞≤n
+-monoʳ-≤ ℕ[ m ] (ℕ≤ℕ x≤y) = ℕ≤ℕ (ℕ.+-monoʳ-≤ m x≤y)

lemma : {n : ℕ} {c₁ c₂ : 1 ⇨ 1}
    → (pf₁ : extract c₁ ≤ ℕ[ n ])
    → (pf₂ : extract c₂ ≤ ℕ[ n ])
    →  extract (⟨▲⟩ ∘ (c₁ ▵ c₂)) ≤ ℕ[ ℕ.suc n ]
lemma {n} {c₁@((a ∷ []) ∷ [])} {c₂@((b ∷ []) ∷ [])} pf₁ pf₂ =
  begin
    extract (⟨▲⟩ ∘ (c₁ ▵ c₂))
  ≡⟨⟩
    extract ( (replicate ℕ[ 1 ] ∷ []) ∘ ((a ∷ []) ∷ (b ∷ []) ∷ []))
  ≡⟨⟩
    extract ((((replicate ℕ[ 1 ]) · (a ∷ b ∷ [])) ∷ []) ∷ [])
  ≡⟨⟩
    (replicate ℕ[ 1 ]) · (a ∷ b ∷ [])
  ≡⟨ dot-⊔ ℕ[ 1 ] (a ∷ b ∷ [])  ⟩
    ℕ[ 1 ] + ⊔-vec (a ∷ b ∷ [])
  ≡⟨⟩
    ℕ[ 1 ] + (a ⊔ ⊔-vec (b ∷ []))
  ≡⟨⟩
    ℕ[ 1 ] + (a ⊔ (b ⊔ ⊔-vec []))
  ≡⟨⟩
    ℕ[ 1 ] + (a ⊔ (b ⊔ ⁻∞))
  ≡⟨⟩
    ℕ[ 1 ] + (extract c₁ ⊔ (extract c₂ ⊔ ⁻∞))
  ≤⟨ +-monoʳ-≤ ℕ[ 1 ] (⊔-monoˡ-≤ (extract c₂ ⊔ ⁻∞) pf₁) ⟩
    ℕ[ 1 ] + (ℕ[ n ] ⊔ (extract c₂ ⊔ ⁻∞))
  ≤⟨ +-monoʳ-≤ ℕ[ 1 ] (⊔-monoʳ-≤ ℕ[ n ] (⊔-monoˡ-≤ ⁻∞ pf₂)) ⟩
    ℕ[ 1 ] + (ℕ[ n ] ⊔ (ℕ[ n ] ⊔ ⁻∞))
  ≡⟨⟩
      ℕ[ 1 ] + (ℕ[ n ] ⊔ ℕ[ n ])
  ≡⟨ cong (ℕ[ 1 ] +_) (⊔-idem ℕ[ n ]) ⟩
     ℕ[ 1 ] + ℕ[ n ]
  ≡⟨⟩
    ℕ[ ℕ.suc n ]
  ∎
  where
    open import Relation.Binary.Reasoning.PartialOrder ≤-poset
    open IsSemiring ⦃ … ⦄

thm : {n : ℕ} → (pt : PT T1 n) → extract (combine pt) ≤ ℕ[ n ]
thm nil                = ⁻∞≤n
thm (leaf a)           = ℕ≤ℕ z≤n
thm {n} (fork (pt1 , pt2)) =
  let (a , b) = (thm pt1 , thm pt2)
  in lemma {c₁ = combine pt1} a b
