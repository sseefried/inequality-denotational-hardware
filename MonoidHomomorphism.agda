{-# OPTIONS --without-K --safe #-}

module MonoidHomomorphism where

open import Data.Product
open import Level using (Level) renaming (suc to lsuc)
open import Algebra.Bundles
open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Morphism.Structures


private
  variable
    c ℓ : Level

open import Algebra.Core using (Op₂)

record PreRawMonoid c : Set (lsuc c) where
   infixl 7 _∙_
   field
      Carrier : Set c
      _∙_ : Op₂ Carrier
      ε   : Carrier

record MonoidLawTransfer ⦃ PM₁ : PreRawMonoid c ⦄ ⦃ M₂ : RawMonoid c ℓ ⦄ : Set where
  open PreRawMonoid PM₁ renaming (Carrier to A; _∙_ to _∙_; ε to ε₁)
  open RawMonoid    M₂  renaming (Carrier to B; _≈_ to _≈₂_;  _∙_ to _◦_; ε to ε₂)

  module LawTransfer (⟦_⟧ : A → B) where

    _≈₁_ : A → A → Set ℓ
    a ≈₁ b = ⟦ a ⟧ ≈₂ ⟦ b ⟧

    M₁ : RawMonoid c ℓ
    M₁ = record { Carrier = A ; _≈_ = _≈₁_ ; _∙_ = _∙_ ; ε = ε₁ }

    lawTransfer : IsMonoidHomomorphism M₁ M₂ ⟦_⟧ → IsMonoid _≈₂_ _◦_ ε₂ → IsMonoid _≈₁_ _∙_ ε₁
    lawTransfer monoid-homo is-monoid₂ =
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
        open IsMonoidHomomorphism ⦃ … ⦄ public
        open IsMonoid ⦃ … ⦄ public
        instance
          _ : IsMonoidHomomorphism M₁ M₂ ⟦_⟧
          _ = monoid-homo

          _ : IsMonoid _≈₂_ _◦_ ε₂
          _ = is-monoid₂

        open import Relation.Binary.Reasoning.Setoid (setoid)

        ∙-congruent : Congruent₂ _≈₁_ _∙_
        ∙-congruent {x} {y} {u} {v} x≈₁y u≈₁v =
          begin
            ⟦ x ∙ u ⟧
          ≈⟨ homo x u ⟩
            ⟦ x ⟧ ◦ ⟦ u ⟧
          ≈⟨ ∙-cong x≈₁y u≈₁v ⟩
            ⟦ y ⟧ ◦ ⟦ v ⟧
          ≈⟨ sym (homo y v) ⟩
            ⟦ y ∙ v ⟧
          ∎

        ∙-identityˡ : LeftIdentity _≈₁_ ε₁ _∙_
        ∙-identityˡ x =
          begin
            ⟦ ε₁ ∙ x ⟧
          ≈⟨ homo ε₁ x  ⟩
            ⟦ ε₁ ⟧ ◦ ⟦ x ⟧
          ≈⟨ ∙-congʳ ε-homo ⟩
            ε₂ ◦ ⟦ x ⟧
          ≈⟨ identityˡ ⟦ x ⟧ ⟩
            ⟦ x ⟧
          ∎

        ∙-identityʳ : RightIdentity _≈₁_ ε₁ _∙_
        ∙-identityʳ x =
          begin
            ⟦ x ∙ ε₁ ⟧
          ≈⟨ homo x ε₁ ⟩
            ⟦ x ⟧ ◦ ⟦ ε₁ ⟧
          ≈⟨ ∙-congˡ ε-homo ⟩
            ⟦ x ⟧ ◦ ε₂
          ≈⟨ identityʳ ⟦ x ⟧ ⟩
            ⟦ x ⟧
          ∎

        ∙-assoc : Associative _≈₁_ _∙_
        ∙-assoc x y z =
          begin
            ⟦ (x ∙ y) ∙ z ⟧
          ≈⟨ homo (x ∙ y) z ⟩
            ⟦ x ∙ y ⟧ ◦ ⟦ z ⟧
          ≈⟨ ∙-congʳ (homo x y) ⟩
            (⟦ x ⟧ ◦ ⟦ y ⟧) ◦ ⟦ z ⟧
          ≈⟨ assoc ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
            ⟦ x ⟧ ◦ (⟦ y ⟧ ◦ ⟦ z ⟧)
          ≈⟨ sym  (∙-congˡ (homo y z)) ⟩
            ⟦ x ⟧ ◦ ⟦ y ∙ z ⟧
          ≈⟨ sym (homo x (y ∙ z)) ⟩
            ⟦ x ∙ (y ∙ z) ⟧
          ∎
