open import Level
open import Algebra.Bundles

module Matrix (sr : RawSemiring 0ℓ 0ℓ) where
  open import Data.Nat hiding (_+_; _*_)
  import Data.Nat as ℕ
  open import Data.Vec
  open import Data.Product using (_×_; _,_)
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  Matrix : Set → ℕ → ℕ → Set
  Matrix A m n =  Vec (Vec A n) m

  open RawSemiring ⦃ … ⦄ public
  instance
    _ : RawSemiring 0ℓ 0ℓ
    _ = sr

  A : Set
  A = Carrier

  _∙_ : {n : ℕ} → Vec A n → Vec A n → A
  _∙_ {n} v₁ v₂ = foldl _ _+_ 0# (zipWith _*_ v₁ v₂)

  -- objects are ℤ
  -- morphisms are matrices
  -- composition is matrix multiplication

  cross : ∀ {A} {m n : ℕ} → Vec A m → Vec A n → Matrix (A × A) m n
  cross {m = zero} _ _ = []
  cross {m = suc m} (x₁ ∷ x₁s) x₂s =  (map (λ x₂ → (x₁ , x₂)) x₂s) ∷ cross x₁s x₂s

  identityMatrix : {n : ℕ}  → Matrix A n n
  identityMatrix = map 1-in-pos indices
    where
      1-in-pos : {n : ℕ} → ℕ → Vec A n
      1-in-pos {zero} _ = []
      1-in-pos {suc n} m with m ℕ.≟ n
      ... | yes refl = 1# ∷ 1-in-pos m
      ... | no _     = 0# ∷ 1-in-pos m

      indices : {n : ℕ} → Vec ℕ n
      indices {zero}  = []
      indices {suc n} = n ∷ indices {n}

  _⨉_ : {m n p : ℕ} → Matrix A m n → Matrix A n p → Matrix A m p
  [] ⨉ _ = []
  _⨉_ {suc m} (v₁ ∷ m₁) m₂ = map (v₁ ∙_) (transpose m₂) ∷ m₁ ⨉ m₂

  zeroMatrix : {m n : ℕ} → Matrix A m n
  zeroMatrix = replicate (replicate 0#)

  -- [A | B]
  _↔_ : {m n p : ℕ} → Matrix A m n → Matrix A m p → Matrix A m (n ℕ.+ p)
  _↔_ = zipWith _++_

  columnOf : {n : ℕ} → A → Matrix A 1 n
  columnOf a = replicate a ∷ []

  zeroColumn : {n : ℕ} → Matrix A 1 n
  zeroColumn = replicate 0# ∷ []
