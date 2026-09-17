# Cancelling the boundary of an evaluated square

These identities use only vertical composition of isomorphisms. Keeping
them independent of the evaluated functors makes the subsequent mate
calculations shorter and bounds the size of their elaboration problems.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

abstract
  append-four : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (A : =₁ a₄ a₅) (B : =₁ a₃ a₄) (C : =₁ a₂ a₃)
    (D : =₁ a₁ a₂) (E : =₁ a₀ a₁) →
    =₂ ((A ∙ (B ∙ (C ∙ D))) ∙ E) (A ∙ (B ∙ (C ∙ (D ∙ E))))
  append-four A B C D E = isoComp-cong (idIso A) (isoComp-cong (idIso B) (isoComp-assoc-at C D E)) ∙
    (isoComp-cong (idIso A) (isoComp-assoc-at B (C ∙ D) E) ∙ isoComp-assoc-at A (B ∙ (C ∙ D)) E)

  cancel-mate : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (A : =₁ a₅ a₄) (B : =₁ a₄ a₃) (C : =₁ a₂ a₃)
    (B⁻ : =₁ a₃ a₄) (U : =₁ a₁ a₂) (r : =₁ a₀ a₁) (tail : =₁ a₀ a₅) →
    =₂ B⁻ (invIso B) → =₂ (U ∙ r) (invIso C ∙ (B ∙ (A ∙ tail))) →
    =₂ ((invIso A ∙ (B⁻ ∙ (C ∙ U))) ∙ r) tail
  cancel-mate A B C B⁻ U r tail inverse square = cancel-left A tail ∙
    (isoComp-cong (idIso (invIso A))
      (cancel-left B (A ∙ tail) ∙ isoComp-cong inverse (idIso (B ∙ (A ∙ tail)))) ∙
    (isoComp-cong (idIso (invIso A)) (isoComp-cong (idIso B⁻) (cancel-inverse C (B ∙ (A ∙ tail)))) ∙
    (isoComp-cong (idIso (invIso A)) (isoComp-cong (idIso B⁻) (isoComp-cong (idIso C) square)) ∙
      append-four (invIso A) B⁻ C U r)))

  cancel-three : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (A : =₁ a₁ a₂) (B : =₁ a₂ a₃) (C : =₁ a₃ a₄) (u : =₁ a₀ a₁) →
    =₂ (((invIso A ∙ invIso B) ∙ invIso C) ∙ (C ∙ (B ∙ (A ∙ u)))) u
  cancel-three A B C u = cancel-left A u ∙
    (isoComp-cong (idIso (invIso A)) (cancel-left B (A ∙ u)) ∙
    (isoComp-assoc-at (invIso A) (invIso B) (B ∙ (A ∙ u)) ∙
    (isoComp-cong (idIso (invIso A ∙ invIso B)) (cancel-left C (B ∙ (A ∙ u))) ∙
      isoComp-assoc-at (invIso A ∙ invIso B) (invIso C) (C ∙ (B ∙ (A ∙ u))))))

  cancel-three-images : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (A : =₁ a₁ a₂) (B : =₁ a₂ a₃) (C : =₁ a₃ a₄) (u : =₁ a₀ a₁)
    (A⁻ : =₁ a₂ a₁) (I : =₁ a₃ a₃) →
    =₂ A⁻ (invIso A) → =₂ I (idIso a₃) →
    =₂ (((A⁻ ∙ invIso B) ∙ (I ∙ invIso C)) ∙ (C ∙ (B ∙ (A ∙ u)))) u
  cancel-three-images A B C u A⁻ I inverse identity = cancel-three A B C u ∙
    isoComp-cong
      (isoComp-cong (isoComp-cong inverse (idIso (invIso B)))
        (isoComp-unitˡ-at (invIso C) ∙ isoComp-cong identity (idIso (invIso C))))
      (idIso (C ∙ (B ∙ (A ∙ u))))

  close-paste : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (T : =₁ a₄ a₃) (P : =₁ a₁ a₄) (z : =₁ a₀ a₁)
    (R : =₁ a₂ a₃) (S : =₁ a₁ a₂) (r : =₁ a₀ a₂) (t : =₁ a₀ a₃) →
    =₂ (T ∙ P) (R ∙ S) → =₂ (S ∙ z) r → =₂ (R ∙ r) t →
    =₂ ((T ∙ P) ∙ z) t
  close-paste T P z R S r t pasted source action = action ∙
    (isoComp-cong (idIso R) source ∙
      (isoComp-assoc-at R S z ∙ isoComp-cong pasted (idIso z)))
```
