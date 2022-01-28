open import Level
open import Algebra.Bundles

module Matrix (s : RawSemiring 0ℓ 0ℓ) where
  open import Data.Nat hiding (_+_; _*_)
  import Data.Nat as ℕ
  open import Data.Vec
  open import Data.Product using (_×_; _,_)
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  open RawSemiring ⦃ … ⦄ public renaming (Carrier to A)

  private
    MatrixPoly : Set → ℕ → ℕ → Set
    MatrixPoly A m n = Vec (Vec A n) m

  instance
    _ : RawSemiring 0ℓ 0ℓ
    _ = s

  Matrix : ℕ → ℕ → Set
  Matrix = MatrixPoly A

  private
    _·_ : {n : ℕ} → Vec A n → Vec A n → A
    _·_ {n} v₁ v₂ = foldl _ _+_ 0# (zipWith _*_ v₁ v₂)

    cross : ∀ {A} {m n : ℕ} → Vec A m → Vec A n → MatrixPoly (A × A) m n
    cross {m = zero} _ _ = []
    cross {m = suc m} (x₁ ∷ x₁s) x₂s =  (map (λ x₂ → (x₁ , x₂)) x₂s) ∷ cross x₁s x₂s

  identity : {n : ℕ}  → Matrix n n
  identity = map 1-in-pos indices
    where
      1-in-pos : {n : ℕ} → ℕ → Vec A n
      1-in-pos {zero} _ = []
      1-in-pos {suc n} m with m ℕ.≟ n
      ... | yes refl = 1# ∷ 1-in-pos m
      ... | no _     = 0# ∷ 1-in-pos m

      indices : {n : ℕ} → Vec ℕ n
      indices {zero}  = []
      indices {suc n} = n ∷ indices {n}

  _∙_ : {m n p : ℕ} → Matrix m n → Matrix n p → Matrix m p
  [] ∙ _ = []
  _∙_ {suc m} (v₁ ∷ m₁) m₂ = map (v₁ ·_) (transpose m₂) ∷ m₁ ∙ m₂

  allZero : {m n : ℕ} → Matrix m n
  allZero = replicate (replicate 0#)

  -- [A | B]
  _↔_ : {m n p : ℕ} → Matrix m n → Matrix m p → Matrix m (n ℕ.+ p)
  _↔_ = zipWith _++_

  -- [A]
  -- [-]
  -- [B]

  _↕_ : {m n p : ℕ} → Matrix m p → Matrix n p → Matrix (m ℕ.+ n) p
  _↕_ = _++_

  columnOf : {n : ℕ} → A → Matrix 1 n
  columnOf a = replicate a ∷ []

  zeroColumn : {n : ℕ} → Matrix 1 n
  zeroColumn = replicate 0# ∷ []
