# Restriction and the core of a functor category

The preferred equivalence between a mapping anima and the core of its
functor category commutes with restriction. Uncurrying reduces the
comparison to naturality of the canonical core inclusion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.FunctorCoreRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPre; funPre-uncurry)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M

module Restrict {A B : CAT} (f : MAP A B) (D : CAT) where
  module Source = CoreOfFun B D
  module Target = CoreOfFun A D

  abstract
    uncurrying-natural : (Target.uncurrying ∘ mapPost {C = One} (funPre {D = D} f)) =₁
      (mapPre f ∘ Source.uncurrying)
    uncurrying-natural = mapReflect (core-isAn (Fun B D)) _ _ (right ⁻¹ ∙ left)
      where
      left : mapUncurry (Target.uncurrying ∘ mapPost {C = One} (funPre {D = D} f)) =₁
        (funUncurry (coreInclusion (Fun B D)) ∘ productMap (id (Core (Fun B D))) f)
      left = funPre-uncurry f (coreInclusion (Fun B D)) ∙
        (funUncurry-cong (coreInclusion-natural (funPre f)) ∙
          ((funUncurry-restrict (coreInclusion (Fun A D)) (mapPost (funPre f))) ⁻¹ ∙
            ((Target.uncurrying-evaluation ▷ productMap (mapPost (funPre f)) (id A)) ∙
              mapUncurry-restrict Target.uncurrying (mapPost (funPre f)))))
      right : mapUncurry (mapPre f ∘ Source.uncurrying) =₁
        (funUncurry (coreInclusion (Fun B D)) ∘ productMap (id (Core (Fun B D))) f)
      right = (Source.uncurrying-evaluation ▷ productMap (id (Core (Fun B D))) f) ∙
        mapPre-uncurry f Source.uncurrying

  source-β : (Source.uncurrying ∘ Source.comparison) =₁ id (Map B D)
  source-β = (IsEquiv.retractionIso Source.uncurrying-isEquiv) ⁻¹
  target-β : (Target.uncurrying ∘ Target.comparison) =₁ id (Map A D)
  target-β = (IsEquiv.retractionIso Target.uncurrying-isEquiv) ⁻¹

  abstract
    comparison-natural : (mapPost (funPre f) ∘ Source.comparison) =₁ (Target.comparison ∘ mapPre f)
    comparison-natural = equiv-reflect Target.uncurrying-isEquiv _ _ (right ⁻¹ ∙ left)
      where
      left : (Target.uncurrying ∘ (mapPost (funPre f) ∘ Source.comparison)) =₁ mapPre f
      left = comp-unitʳ (mapPre f) ∙
        ((mapPre f ◁ source-β) ∙
          (comp-assoc Source.comparison Source.uncurrying (mapPre f) ∙
            ((uncurrying-natural ▷ Source.comparison) ∙
              (comp-assoc Source.comparison (mapPost (funPre f)) Target.uncurrying) ⁻¹)))
      right : (Target.uncurrying ∘ (Target.comparison ∘ mapPre f)) =₁ mapPre f
      right = comp-unitˡ (mapPre f) ∙
        ((target-β ▷ mapPre f) ∙ (comp-assoc (mapPre f) Target.comparison Target.uncurrying) ⁻¹)

  abstract
    mapping-isEquiv : IsEquiv (funPre {D = D} f) → IsEquiv (mapPre {D = D} f)
    mapping-isEquiv ef = equiv-cancel-right Source.uncurrying (mapPre f) Source.uncurrying-isEquiv
      (equiv-transport uncurrying-natural
        (equiv-compose (mapPost {C = One} (funPre {D = D} f)) Target.uncurrying
          (mapPost-isEquiv (funPre f) ef) Target.uncurrying-isEquiv))
```
