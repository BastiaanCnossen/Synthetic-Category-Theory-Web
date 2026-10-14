# Units in product separation

Separating the identity in the parameter coordinate agrees with the
left and right product unit comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.ProductSeparationUnits
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SectionFrames 𝒯 using (identity-unitors)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (productMap-unitˡ; productMap-unitʳ)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {B C : CAT} (X : CAT) (r : MAP B C) where
  W : MAP (X × B) (X × C)
  W = productMap (id X) r
  A₀ = productMap-cong (comp-unitʳ (id X)) (comp-unitˡ r)
  B₀ = productMap-comp (id X) (id X) r (id C)
  C₀ = productMap-cong (comp-unitˡ (id X)) (comp-unitʳ r)
  D₀ = productMap-comp (id X) (id X) (id B) r
  left = comp-unitˡ W ∙ (productMap-id X C ▷ W)
  right = comp-unitʳ W ∙ (W ◁ productMap-id X B)
  separation = productMap-separate (id X) r

  abstract
    left-normal : (A₀ ∙ B₀) =₂ left
    left-normal = productMap-unitˡ (id X) r ∙
      isoComp-cong (productMap-cong-Iso₂ (identity-unitors X) (idIso (comp-unitˡ r))) (idIso B₀)

    right-normal : (C₀ ∙ D₀) =₂ right
    right-normal = productMap-unitʳ (id X) r ∙
      isoComp-cong (productMap-cong-Iso₂ ((identity-unitors X) ⁻¹) (idIso (comp-unitʳ r))) (idIso D₀)

    cancellation : ((A₀ ∙ B₀) ∙ separation) =₂ (C₀ ∙ D₀)
    cancellation = cancel-inverse A₀ (C₀ ∙ D₀) ∙
      isoComp-cong (idIso A₀) (cancel-inverse B₀ (A₀ ⁻¹ ∙ (C₀ ∙ D₀))) ∙
      isoComp-assoc-at A₀ B₀ separation

    value : (left ∙ separation) =₂ right
    value = right-normal ∙ cancellation ∙ isoComp-cong (left-normal ⁻¹) (idIso separation)
```
