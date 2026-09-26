# Replacing an identified base functor by the identity

The unit and associativity laws identify a triangle postcomposed with
a functor identified with the identity with its original triangle.
The equation keeps the two specified changes of structure.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.BaseIdentityTriangles
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (lift-base)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-base-outer)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)

module Change {B : CAT} {F : MAP B B} (β : F =₁ id B) where
  structure : {K : CAT} (k : MAP K B) → (F ∘ k) =₁ k
  structure k = comp-unitˡ k ∙ (β ▷ k)

  abstract
    unit : {K G : CAT} (g : MAP G B) (h : MAP K G) (k : MAP K B)
      (b : (g ∘ h) =₁ k) →
      (comp-unitˡ k ∙ lift-base (id B) g h b) =₂ (b ∙ (comp-unitˡ g ▷ h))
    unit g h k b = isoComp-cong (idIso b) (left-unitor-comp h g) ∙
      (isoComp-assoc-at b (comp-unitˡ (g ∘ h)) (comp-assoc h g (id B)) ∙
        (isoComp-cong (postWhisker-id-at b) (idIso (comp-assoc h g (id B))) ∙
          (isoComp-assoc-at (comp-unitˡ k) (id B ◁ b) (comp-assoc h g (id B))) ⁻¹))

    comparison : {K G : CAT} (g : MAP G B) (h : MAP K G) (k : MAP K B)
      (b : (g ∘ h) =₁ k) →
      (structure k ∙ lift-base F g h b) =₂ (b ∙ (structure g ▷ h))
    comparison g h k b = isoComp-cong (idIso b) ((preWhisker-isoComp-at (comp-unitˡ g) (β ▷ g) h) ⁻¹) ∙
      (isoComp-assoc-at b (comp-unitˡ g ▷ h) ((β ▷ g) ▷ h) ∙
        (isoComp-cong (unit g h k b) (idIso ((β ▷ g) ▷ h)) ∙
          ((isoComp-assoc-at (comp-unitˡ k) (lift-base (id B) g h b) ((β ▷ g) ▷ h)) ⁻¹ ∙
            (isoComp-cong (idIso (comp-unitˡ k)) ((lift-base-outer g k h b β) ⁻¹) ∙
              isoComp-assoc-at (comp-unitˡ k) (β ▷ k) (lift-base F g h b)))))
```
