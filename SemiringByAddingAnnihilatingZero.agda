module SemiringByAddingAnnihilatingZero {a} (A : Set a) where

open import Level

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Core using (Op₂)

--
-- The technique below allows me to paramterise Algebra modules just on
-- the A parameter (not the equivalence)
--
module _ (A : Set a) where
  open import Algebra.Structures (_≡_ {A = A}) public
  open import Algebra.Definitions (_≡_ {A = A}) public

module _
           (_+_ : Op₂ A) (_*_ : Op₂ A) (1# : A)
           (*-distrib-+ : _DistributesOver_ A _*_ _+_)
           ⦃ _ : IsCommutativeSemigroup A _+_ ⦄ ⦃ _ : IsMonoid A _*_ 1# ⦄ where

  data A⁺ : Set a where
    0#   : A⁺
    A[_] : A → A⁺

  private
     infixl 6 _+̂_
     infixl 7 _*̂_

     _*̂_ : A⁺ → A⁺ → A⁺
     0# *̂ _ = 0#
     _ *̂ 0# = 0#
     A[ i ] *̂ A[ j ] = A[ i * j ]

     _+̂_ : A⁺ → A⁺ → A⁺
     0# +̂ b = b
     a +̂ 0# = a
     A[ i ] +̂ A[ j ] = A[ i + j ]

     0̂ : A⁺
     0̂ = 0#

     1̂ : A⁺
     1̂ = A[ 1# ]

  module A⁺-isSemiring where

   open import Relation.Binary.PropositionalEquality
   open ≡-Reasoning
   open import Data.Product using (_,_; proj₁; proj₂)

   isSemiring : IsSemiring A⁺ _+̂_ _*̂_ 0̂ 1̂
   isSemiring =
     record
       { isSemiringWithoutAnnihilatingZero =
           record
             { +-isCommutativeMonoid = +̂-isCommutativeMonoid
             ; *-isMonoid = *̂-isMonoid
             ; distrib = *̂-distribˡ-+̂ , *̂-distribʳ-+̂
             }
       ; zero = zeroˡ , zeroʳ
       }
     where
       zeroˡ : (a : A⁺) → 0̂ *̂ a ≡ 0̂
       zeroˡ = λ _ → refl

       zeroʳ : (a : A⁺) → a *̂ 0̂ ≡ 0̂
       zeroʳ = λ {0# → refl; A[ _ ] → refl }

       module _ where
         open IsCommutativeSemigroup ⦃ … ⦄ hiding (refl; sym)
         +̂-identityˡ : (a : A⁺) → (0̂ +̂ a) ≡ a
         +̂-identityˡ = λ a → refl

         +̂-identityʳ : (a : A⁺) → (a +̂ 0̂) ≡ a
         +̂-identityʳ 0# = refl
         +̂-identityʳ A[ n ] = refl

         +̂-assoc : (a b c : A⁺) → (a +̂ b) +̂ c ≡ a +̂ (b +̂ c)
         +̂-assoc A[ a ] A[ b ] A[ c ] = cong A[_] (assoc A a b c)
         +̂-assoc 0# b c  = refl
         +̂-assoc a 0# c =
           begin
             (a +̂ 0̂) +̂ c
           ≡⟨ cong (_+̂ c) (+̂-identityʳ a) ⟩
             a +̂ c
           ≡⟨⟩
             a +̂ (0̂ +̂ c)
           ∎
         +̂-assoc a b 0#  =
           begin
             (a +̂ b) +̂ 0̂
           ≡⟨ +̂-identityʳ (a +̂ b)  ⟩
             a +̂ b
           ≡⟨ cong (a +̂_) (sym (+̂-identityʳ b))  ⟩
             a +̂ (b +̂ 0̂)
           ∎

         +̂-comm : (a b : A⁺) → a +̂ b ≡ b +̂ a
         +̂-comm A[ a ] A[ b ] = cong A[_] (comm a b)
         +̂-comm A[ a ] 0# = refl
         +̂-comm 0# A[ b ] = refl
         +̂-comm 0# 0# = refl

       module _ where
         open IsMonoid ⦃ … ⦄ hiding (refl; sym)

         *̂-assoc : (a b c : A⁺) → (a *̂ b) *̂ c ≡ a *̂ (b *̂ c)
         *̂-assoc A[ a ] A[ b ] A[ c ] = cong A[_] (assoc A a b c)
         *̂-assoc 0# b c  = refl
         *̂-assoc a 0# c  =
           begin
             (a *̂ 0#) *̂ c
           ≡⟨ cong (_*̂ c) (zeroʳ a) ⟩
             0# *̂ c
           ≡⟨⟩
             0#
           ≡⟨ sym (zeroʳ a) ⟩
             a *̂ 0#
           ≡⟨ cong (a *̂_) (sym (zeroˡ c) ) ⟩
             a *̂ (0# *̂ c)
           ∎
         *̂-assoc a b 0# =
           begin
             (a *̂ b) *̂ 0#
           ≡⟨  zeroʳ (a *̂ b) ⟩
             0#
           ≡⟨ sym (zeroʳ a) ⟩
             a *̂ 0#
           ≡⟨ cong (a *̂_) (sym (zeroʳ b))  ⟩
             a *̂ (b *̂ 0#)
           ∎

         *̂-identityˡ : (a : A⁺) → (1̂ *̂ a) ≡ a
         *̂-identityˡ 0# = refl
         *̂-identityˡ A[ a ] = cong A[_] (identityˡ A a)

         *̂-identityʳ : (a : A⁺) → (a *̂ 1̂) ≡ a
         *̂-identityʳ 0# = refl
         *̂-identityʳ A[ a ] = cong A[_] (identityʳ A a)

       *̂-distribˡ-+̂  : (a b c : A⁺) → a *̂ (b +̂ c) ≡ (a *̂ b) +̂ (a *̂ c)
       *̂-distribˡ-+̂ A[ a ] A[ b ] A[ c ] = cong A[_] (*-distribˡ-+ a b c)
         where *-distribˡ-+ = proj₁ *-distrib-+
       *̂-distribˡ-+̂ 0# b c = refl
       *̂-distribˡ-+̂ a 0# c rewrite +̂-identityˡ c rewrite zeroʳ a = refl
       *̂-distribˡ-+̂ a b 0# rewrite +̂-identityʳ b
                           rewrite zeroʳ a
                           rewrite +̂-identityʳ (a *̂ b) = refl

       *̂-distribʳ-+̂  : (a b c : A⁺) → ((b +̂ c) *̂ a) ≡ ((b *̂ a) +̂ (c *̂ a))
       *̂-distribʳ-+̂ A[ a ] A[ b ] A[ c ] = cong A[_] (*-distribʳ-+ a b c)
         where *-distribʳ-+ = proj₂ *-distrib-+
       *̂-distribʳ-+̂ 0# b c rewrite zeroʳ b
                           rewrite zeroʳ c
                           rewrite zeroʳ (b +̂ c) = refl
       *̂-distribʳ-+̂ a 0# c = refl
       *̂-distribʳ-+̂ a b 0# rewrite +̂-identityʳ b
                           rewrite +̂-identityʳ (b *̂ a) = refl

       +̂-isMonoid : IsMonoid A⁺ _+̂_ 0̂
       +̂-isMonoid =
         record
           { isSemigroup =
               record
                 { isMagma = isMagma _+̂_
                 ; assoc = +̂-assoc
                 }
           ; identity = +̂-identityˡ , +̂-identityʳ
           }

       +̂-isCommutativeMonoid : IsCommutativeMonoid A⁺ _+̂_ 0̂
       +̂-isCommutativeMonoid =
         record
           { isMonoid = +̂-isMonoid
           ; comm = +̂-comm
           }

       *̂-isMonoid : IsMonoid A⁺ _*̂_ 1̂
       *̂-isMonoid =
         record
           { isSemigroup =
               record
                 { isMagma = isMagma _*̂_
                 ; assoc = *̂-assoc
                 }
           ; identity = *̂-identityˡ , *̂-identityʳ
           }
