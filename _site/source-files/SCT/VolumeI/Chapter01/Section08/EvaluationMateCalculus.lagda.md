# Cancelling the boundary of an evaluated square

These identities use only vertical composition of isomorphisms. Keeping
them independent of the evaluated functors makes the subsequent mate
calculations shorter and bounds the size of their elaboration problems.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

abstract
  append-four : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (A : a₄ =₁ a₅) (B : a₃ =₁ a₄) (C : a₂ =₁ a₃)
    (D : a₁ =₁ a₂) (E : a₀ =₁ a₁) →
    ((A ∙ (B ∙ (C ∙ D))) ∙ E) =₂ (A ∙ (B ∙ (C ∙ (D ∙ E))))
  append-four A B C D E = isoComp-cong (idIso A) (isoComp-cong (idIso B) (isoComp-assoc-at C D E)) ∙
    (isoComp-cong (idIso A) (isoComp-assoc-at B (C ∙ D) E) ∙ isoComp-assoc-at A (B ∙ (C ∙ D)) E)

  cancel-mate : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (A : a₅ =₁ a₄) (B : a₄ =₁ a₃) (C : a₂ =₁ a₃)
    (B⁻ : a₃ =₁ a₄) (U : a₁ =₁ a₂) (r : a₀ =₁ a₁) (tail : a₀ =₁ a₅) →
    B⁻ =₂ (B ⁻¹) → (U ∙ r) =₂ (C ⁻¹ ∙ (B ∙ (A ∙ tail))) →
    ((A ⁻¹ ∙ (B⁻ ∙ (C ∙ U))) ∙ r) =₂ tail
  cancel-mate A B C B⁻ U r tail inverse square = cancel-left A tail ∙
    (isoComp-cong (idIso (A ⁻¹))
      (cancel-left B (A ∙ tail) ∙ isoComp-cong inverse (idIso (B ∙ (A ∙ tail)))) ∙
    (isoComp-cong (idIso (A ⁻¹)) (isoComp-cong (idIso B⁻) (cancel-inverse C (B ∙ (A ∙ tail)))) ∙
    (isoComp-cong (idIso (A ⁻¹)) (isoComp-cong (idIso B⁻) (isoComp-cong (idIso C) square)) ∙
      append-four (A ⁻¹) B⁻ C U r)))

  cancel-three : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (A : a₁ =₁ a₂) (B : a₂ =₁ a₃) (C : a₃ =₁ a₄) (u : a₀ =₁ a₁) →
    (((A ⁻¹ ∙ B ⁻¹) ∙ C ⁻¹) ∙ (C ∙ (B ∙ (A ∙ u)))) =₂ u
  cancel-three A B C u = cancel-left A u ∙
    (isoComp-cong (idIso (A ⁻¹)) (cancel-left B (A ∙ u)) ∙
    (isoComp-assoc-at (A ⁻¹) (B ⁻¹) (B ∙ (A ∙ u)) ∙
    (isoComp-cong (idIso (A ⁻¹ ∙ B ⁻¹)) (cancel-left C (B ∙ (A ∙ u))) ∙
      isoComp-assoc-at (A ⁻¹ ∙ B ⁻¹) (C ⁻¹) (C ∙ (B ∙ (A ∙ u))))))

  cancel-three-images : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (A : a₁ =₁ a₂) (B : a₂ =₁ a₃) (C : a₃ =₁ a₄) (u : a₀ =₁ a₁)
    (A⁻ : a₂ =₁ a₁) (I : a₃ =₁ a₃) →
    A⁻ =₂ (A ⁻¹) → I =₂ (idIso a₃) →
    (((A⁻ ∙ B ⁻¹) ∙ (I ∙ C ⁻¹)) ∙ (C ∙ (B ∙ (A ∙ u)))) =₂ u
  cancel-three-images A B C u A⁻ I inverse identity = cancel-three A B C u ∙
    isoComp-cong
      (isoComp-cong (isoComp-cong inverse (idIso (B ⁻¹)))
        (isoComp-unitˡ-at (C ⁻¹) ∙ isoComp-cong identity (idIso (C ⁻¹))))
      (idIso (C ∙ (B ∙ (A ∙ u))))

  close-paste : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (T : a₄ =₁ a₃) (P : a₁ =₁ a₄) (z : a₀ =₁ a₁)
    (R : a₂ =₁ a₃) (S : a₁ =₁ a₂) (r : a₀ =₁ a₂) (t : a₀ =₁ a₃) →
    (T ∙ P) =₂ (R ∙ S) → (S ∙ z) =₂ r → (R ∙ r) =₂ t →
    ((T ∙ P) ∙ z) =₂ t
  close-paste T P z R S r t pasted source action = action ∙
    (isoComp-cong (idIso R) source ∙
      (isoComp-assoc-at R S z ∙ isoComp-cong pasted (idIso z)))
```
