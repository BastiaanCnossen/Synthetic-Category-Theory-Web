# The outer unit frame for postcomposition

The image of the right unitor of a postcomposition functor agrees with
evaluating the original identity comparison before postcomposition.
The calculation uses the generic uncurrying unit law and naturality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PostcompositionUnitFrame
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingUnits as UnitImages
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (right-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; preWhisker-id-at)

module At {C D : CAT} (K : CAT) (l : MAP C D) where
  L : MAP (Fun K C) (Fun K D)
  L = funPost l
  e : MAP (Fun K C × K) C
  e = funEval
  J : MAP (Fun K C × K) (Fun K C × K)
  J = productMap (id (Fun K C)) (id K)
  δ : J =₁ id (Fun K C × K)
  δ = productMap-id (Fun K C) K
  β : funUncurry L =₁ (l ∘ e)
  β = funPost-β l
  t : funUncurry (id (Fun K C)) =₁ e
  t = funUncurry-id K C
  q : funUncurry (L ∘ id (Fun K C)) =₁ (funUncurry L ∘ J)
  q = funUncurry-restrict L (id (Fun K C))
  module Images = UnitImages.At 𝒯 M ℱ L

  abstract
    prefix : ((l ◁ t) ∙ comp-assoc J e l) =₂
      (comp-unitʳ (l ∘ e) ∙ ((l ∘ e) ◁ δ))
    prefix = isoComp-cong ((right-unitor-comp e l) ⁻¹) (idIso ((l ∘ e) ◁ δ)) ∙
      (isoComp-assoc-at (l ◁ comp-unitʳ e) (comp-assoc (id _) e l) ((l ∘ e) ◁ δ)) ⁻¹ ∙
      isoComp-cong (idIso (l ◁ comp-unitʳ e)) ((postWhisker-comp-at δ e l) ⁻¹) ∙
      isoComp-assoc-at (l ◁ comp-unitʳ e) (l ◁ (e ◁ δ)) (comp-assoc J e l) ∙
      isoComp-cong (postWhisker-isoComp-at l (comp-unitʳ e) (e ◁ δ)) (idIso (comp-assoc J e l))

    slide : ((comp-unitʳ (l ∘ e) ∙ ((l ∘ e) ◁ δ)) ∙ ((β ▷ J) ∙ q)) =₂
      (β ∙ (comp-unitʳ (funUncurry L) ∙ ((funUncurry L ◁ δ) ∙ q)))
    slide = isoComp-assoc-at β (comp-unitʳ (funUncurry L)) ((funUncurry L ◁ δ) ∙ q) ∙
      isoComp-cong (preWhisker-id-at β) (idIso ((funUncurry L ◁ δ) ∙ q)) ∙
      (isoComp-assoc-at (comp-unitʳ (l ∘ e)) (β ▷ id _) ((funUncurry L ◁ δ) ∙ q)) ⁻¹ ∙
      isoComp-cong (idIso (comp-unitʳ (l ∘ e)))
        (isoComp-assoc-at (β ▷ id _) (funUncurry L ◁ δ) q ∙
          isoComp-cong ((interchange-at β δ) ⁻¹) (idIso q) ∙
          (isoComp-assoc-at ((l ∘ e) ◁ δ) (β ▷ J) q) ⁻¹) ∙
      isoComp-assoc-at (comp-unitʳ (l ∘ e)) ((l ∘ e) ◁ δ) ((β ▷ J) ∙ q)

    comparison : (β ∙ funUncurryIso (comp-unitʳ L)) =₂
      ((l ◁ t) ∙ funPost-uncurry l (id (Fun K C)))
    comparison = (isoComp-cong (idIso β) (Images.right ⁻¹) ∙ slide ∙
      isoComp-cong prefix (idIso ((β ▷ J) ∙ q)) ∙
      (isoComp-assoc-at (l ◁ t) (comp-assoc J e l) ((β ▷ J) ∙ q)) ⁻¹) ⁻¹
```
