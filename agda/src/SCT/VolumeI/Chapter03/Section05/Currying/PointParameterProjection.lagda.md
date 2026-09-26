# The projection of a point parameter

The functor inserting a point into the first coordinate carries a chosen
second-projection witness. Every triangle obtained by restricting a
relative family to that point is the postcomposition of this witness.
This normalization also records its naturality in the structure functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.Section05.Currying.PointParameterProjection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-base-outer)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.UnitRestrictionComposition 𝒯 M using (unit-lift-assoc)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies 𝒯 M ℱ P using (point-parameter)
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-id-at)
module PS = Projections 𝒯

module Point {X A : CAT} (z : Obj-abs X) where
  H : MAP (One × A) (X × A)
  H = productMap z (id A)
  i : MAP A (One × A)
  i = oneProduct-in A
  K : MAP A (X × A)
  K = H ∘ i
  projection : (pr₂ ∘ K) =₁ id A
  projection = PS.compose-base pr₂ H (parameter-base z A) i (oneProduct-retraction A)

  triangle : {S : CAT} (f : MAP A S) → ((f ∘ pr₂ {C = X}) ∘ K) =₁ f
  triangle f = FunctorLift.comparison (point-parameter f z)

  abstract
    normalization : {S : CAT} (f : MAP A S) → triangle f =₂
      (comp-unitʳ f ∙ PS.lift-base f pr₂ K projection)
    normalization f = isoComp-cong (idIso (comp-unitʳ f))
        (PS.lift-compose f pr₂ H i (parameter-base z A) (oneProduct-retraction A)) ∙
      isoComp-assoc-at (comp-unitʳ f)
        (PS.lift-base f pr₂ i (oneProduct-retraction A))
        ((PS.lift-base f pr₂ H (parameter-base z A) ▷ i) ∙
          (comp-assoc i H (f ∘ pr₂)) ⁻¹)

    outer : {S : CAT} {f g : MAP A S} (α : f =₁ g) →
      (triangle g ∙ ((α ▷ pr₂) ▷ K)) =₂ (α ∙ triangle f)
    outer {f = f} {g} α = isoComp-cong (idIso α) ((normalization f) ⁻¹) ∙
      (isoComp-assoc-at α (comp-unitʳ f) (PS.lift-base f pr₂ K projection) ∙
        (isoComp-cong (preWhisker-id-at α) (idIso (PS.lift-base f pr₂ K projection)) ∙
          ((isoComp-assoc-at (comp-unitʳ g) (α ▷ id A) (PS.lift-base f pr₂ K projection)) ⁻¹ ∙
            (isoComp-cong (idIso (comp-unitʳ g)) (lift-base-outer pr₂ (id A) K projection α) ∙
              (isoComp-assoc-at (comp-unitʳ g) (PS.lift-base g pr₂ K projection) ((α ▷ pr₂) ▷ K) ∙
                isoComp-cong (normalization g) (idIso ((α ▷ pr₂) ▷ K)))))))

    composite : {B C : CAT} (f : MAP A B) (g : MAP B C) →
      triangle (g ∘ f) =₂
        (PS.lift-base g (f ∘ pr₂) K (triangle f) ∙ (comp-assoc pr₂ f g ▷ K))
    composite f g = isoComp-cong
        (isoComp-cong (postWhisker g ◁ (normalization f) ⁻¹) (idIso (comp-assoc K (f ∘ pr₂) g)))
        (idIso (comp-assoc pr₂ f g ▷ K)) ∙
      (unit-lift-assoc pr₂ K projection f g ∙ normalization (g ∘ f))
```
