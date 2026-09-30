# Restriction frames of a curried interval diagram

Recovering the diagram of a curried expression changes its endpoint frame
by the currying beta comparison. After a further uncurrying, naturality of
restriction transports this same comparison through the frame.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurriedRestrictionFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrameNaturality as Natural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {Γ X C : CAT} (H : MAP (Γ × [1]) (Fun X C))
  (z : Obj-abs [1]) {f : MAP Γ (Fun X C)} (p : (H ∘ insert z) =₁ f) where
  arrow : MAP Γ (Ar (Fun X C))
  arrow = funCurry H
  old = funUncurry arrow
  β : old =₁ H
  β = funCurry-β H
  i = insert {X = Γ} z
  s = productMap i (id X)
  Q = evaluate-uncurry z arrow
  b = β ▷ i
  frame : (old ∘ i) =₁ f
  frame = (p ∙ evaluate-curry z H) ∙ Q ⁻¹

  abstract
    frame-normalization : frame =₂ (p ∙ b)
    frame-normalization = cancel-right Q (p ∙ b) ∙
      isoComp-cong ((isoComp-assoc-at p b Q) ⁻¹) (idIso (Q ⁻¹))

    comparison : (funUncurryIso frame ∙ (funUncurry-restrict old i) ⁻¹) =₂
      ((funUncurryIso p ∙ (funUncurry-restrict H i) ⁻¹) ∙ (funUncurryIso β ▷ s))
    comparison = Natural.At.comparison 𝒯 M ℱ β i p ∙
      isoComp-cong (funUncurry-Iso₂ frame-normalization) (idIso ((funUncurry-restrict old i) ⁻¹))
```
