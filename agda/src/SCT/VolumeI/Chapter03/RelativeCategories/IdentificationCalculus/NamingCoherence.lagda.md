# Coherence of naming and decoding

Decoding respects composition of identifications and the specified
postcomposition comparison. These finite calculations let native
triangles be compared in the relative mapping anima without discarding
their matching identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingCoherence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingCompatibility 𝒯 M ℱ using (funPost-uncurry-natural)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ using (decodeFun-post)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications 𝒯 M ℱ
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

abstract
  decodeFunIso-comp : {C D : CAT} {x y z : Obj-abs (Fun C D)}
    (β : y =₁ z) (α : x =₁ y) →
    decodeFunIso (β ∙ α) =₂ (decodeFunIso β ∙ decodeFunIso α)
  decodeFunIso-comp {C} β α = isoComp-cong ((decodeFunIso-at β) ⁻¹) ((decodeFunIso-at α) ⁻¹) ∙
    (preWhisker-isoComp-at (funUncurryIso β) (funUncurryIso α) (oneProduct-in C) ∙
      ((preWhisker (oneProduct-in C) ◁ funUncurryIso-comp β α) ∙ decodeFunIso-at (β ∙ α)))

module DecodePost {B C D : CAT} (g : MAP C D) {u v : Obj-abs (Fun B C)} (α : u =₁ v) where
  i : MAP B (One × B)
  i = oneProduct-in B
  ηu : funUncurry (funPost g ∘ u) =₁ (g ∘ funUncurry u)
  ηu = funPost-uncurry g u
  ηv : funUncurry (funPost g ∘ v) =₁ (g ∘ funUncurry v)
  ηv = funPost-uncurry g v
  Au : ((g ∘ funUncurry u) ∘ i) =₁ (g ∘ decodeFun u)
  Au = comp-assoc i (funUncurry u) g
  Av : ((g ∘ funUncurry v) ∘ i) =₁ (g ∘ decodeFun v)
  Av = comp-assoc i (funUncurry v) g
  raw : funUncurry (funPost g ∘ u) =₁ funUncurry (funPost g ∘ v)
  raw = funUncurryIso (funPost g ◁ α)
  decoded : funUncurry u =₁ funUncurry v
  decoded = funUncurryIso α

  abstract
    natural : (decodeFun-post g v ∙ decodeFunIso (funPost g ◁ α)) =₂
      ((g ◁ decodeFunIso α) ∙ decodeFun-post g u)
    natural = isoComp-cong (postWhisker g ◁ (decodeFunIso-at α) ⁻¹) (idIso (decodeFun-post g u)) ∙
      (isoComp-assoc-at (g ◁ (decoded ▷ i)) Au (ηu ▷ i) ∙
        (isoComp-cong (whisker-mixed-at decoded i g) (idIso (ηu ▷ i)) ∙
          ((isoComp-assoc-at Av ((g ◁ decoded) ▷ i) (ηu ▷ i)) ⁻¹ ∙
            (isoComp-cong (idIso Av) (preWhisker-isoComp-at (g ◁ decoded) ηu i) ∙
              (isoComp-cong (idIso Av) (preWhisker i ◁ funPost-uncurry-natural g α) ∙
                (isoComp-cong (idIso Av) ((preWhisker-isoComp-at ηv raw i) ⁻¹) ∙
                  (isoComp-assoc-at Av (ηv ▷ i) (raw ▷ i) ∙
                    isoComp-cong (idIso (decodeFun-post g v)) (decodeFunIso-at (funPost g ◁ α)))))))))
```
