{-# OPTIONS --without-K --safe #-}

module MonoidHomomorphism where

open import Data.Product
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

open import Algebra.Core using (Op₂)

record Monoid (A : Set) : Set₁ where
   infixr 29 _∙_
   field
      _∙_ : Op₂ A
      ε : A

open Monoid ⦃ … ⦄  public

record MonoidHomomorphism (⟦_⟧ : A → B) (_≈₂_ : B → B → Set)
                          ⦃ _ : Monoid A ⦄ ⦃ _ : Monoid B ⦄ : Set where
  field
    monoid-homo-id : ⟦ ε ⟧ ≈₂ ε
    monoid-homo-op : ∀ x y → ⟦ x ∙ y ⟧ ≈₂ ⟦ x ⟧ ∙ ⟦ y ⟧

  open import Algebra.Definitions
  open import Algebra.Structures
  open IsMonoid ⦃ … ⦄ public
  open Level
  open import Relation.Binary

  _≈₁_ : A → A → Set
  a ≈₁ b = ⟦ a ⟧ ≈₂ ⟦ b ⟧

  is-monoid₁ : IsMonoid _≈₂_ _∙_ ε → IsMonoid _≈₁_ _∙_ ε
  is-monoid₁ is-monoid₂ =
    record
      { isSemigroup =
          record
            { isMagma =
                record
                  { isEquivalence = record { refl = refl; sym = sym; trans = trans }
                  ; ∙-cong = ∙-congruent
                  }
            ; assoc = ∙-assoc
            }
      ; identity = ∙-identityˡ , ∙-identityʳ
      }
    where
      instance
        _ : IsMonoid _≈₂_ _∙_ ε
        _ = is-monoid₂

      open import Relation.Binary.Reasoning.Setoid (setoid)

      ∙-congruent : Congruent₂ _≈₁_ _∙_
      ∙-congruent {x} {y} {u} {v} x≈₁y u≈₁v =
        begin
          ⟦ x ∙ u ⟧
        ≈⟨ monoid-homo-op x u ⟩
          ⟦ x ⟧ ∙ ⟦ u ⟧
        ≈⟨ ∙-cong x≈₁y u≈₁v ⟩
          ⟦ y ⟧ ∙ ⟦ v ⟧
        ≈⟨ sym (monoid-homo-op y v) ⟩
          ⟦ y ∙ v ⟧
        ∎

      ∙-identityˡ : LeftIdentity _≈₁_ ε _∙_
      ∙-identityˡ x =
        begin
          ⟦ ε ∙ x ⟧
        ≈⟨ monoid-homo-op ε x  ⟩
          ⟦ ε ⟧ ∙ ⟦ x ⟧
        ≈⟨ ∙-congʳ monoid-homo-id ⟩
          ε ∙ ⟦ x ⟧
        ≈⟨ identityˡ ⟦ x ⟧ ⟩
          ⟦ x ⟧
        ∎

      ∙-identityʳ : RightIdentity _≈₁_ ε _∙_
      ∙-identityʳ x =
        begin
          ⟦ x ∙ ε ⟧
        ≈⟨ monoid-homo-op x ε ⟩
          ⟦ x ⟧ ∙ ⟦ ε ⟧
        ≈⟨ ∙-congˡ monoid-homo-id ⟩
          ⟦ x ⟧ ∙ ε
        ≈⟨ identityʳ ⟦ x ⟧ ⟩
          ⟦ x ⟧
        ∎

      ∙-assoc : Associative _≈₁_ _∙_
      ∙-assoc x y z =
        begin
          ⟦ (x ∙ y) ∙ z ⟧
        ≈⟨ monoid-homo-op (x ∙ y) z ⟩
          ⟦ x ∙ y ⟧ ∙ ⟦ z ⟧
        ≈⟨ ∙-congʳ (monoid-homo-op x y) ⟩
          (⟦ x ⟧ ∙ ⟦ y ⟧) ∙ ⟦ z ⟧
        ≈⟨ assoc ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
          ⟦ x ⟧ ∙ (⟦ y ⟧ ∙ ⟦ z ⟧)
        ≈⟨ sym  (∙-congˡ (monoid-homo-op y z)) ⟩
          ⟦ x ⟧ ∙ ⟦ y ∙ z ⟧
        ≈⟨ sym (monoid-homo-op x (y ∙ z)) ⟩
          ⟦ x  ∙  (y ∙ z) ⟧
        ∎
