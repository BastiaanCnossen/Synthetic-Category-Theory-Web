# Choosing the unit with a prescribed triangle identity

The proof of `lem:Equivalence_Inverse_Over_Base` first adjusts the unit of
an equivalence to a chosen counit. Lifting through postwhiskering supplies
the unit and its specified image. Cancelling the associator and counit
then proves the triangle equation below.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.EquivalenceUnit
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module ChosenUnit {C D : CAT} (F : MAP C D) (e : IsEquiv F)
  (G : MAP D C) (ε : (F ∘ G) =₁ (id D)) where
  associator = comp-assoc F G F
  close = comp-unitˡ F ∙ (ε ▷ F)
  image = associator ∙ (close ⁻¹ ∙ comp-unitʳ F)
  chosen = postWhisker-lift F e image

  unit : (id C) =₁ (G ∘ F)
  unit = FunctorLift.lift chosen

  unit-image : (F ◁ unit) =₂ image
  unit-image = FunctorLift.comparison chosen

  triangle : (close ∙ (associator ⁻¹ ∙ (F ◁ unit))) =₂ (comp-unitʳ F)
  triangle = cancel-inverse close (comp-unitʳ F) ∙
    (isoComp-cong (idIso close) (cancel-left associator (close ⁻¹ ∙ comp-unitʳ F)) ∙
      isoComp-cong (idIso close) (isoComp-cong (idIso (associator ⁻¹)) unit-image))

  equivalence : IsEquiv F
  equivalence = record { inverse = G ; sectionIso = unit ; retractionIso = ε ⁻¹ }
```
