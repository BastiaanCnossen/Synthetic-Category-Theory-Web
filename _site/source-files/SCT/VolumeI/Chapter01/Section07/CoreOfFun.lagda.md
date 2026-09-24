# The core of a functor category

For `core_of_Fun_is_Map`, first uncurry on the terminal parameter and
restrict along `C → One × C`. This gives the equivalence from the core
to the mapping anima. Its inverse is the preferred comparison. We check
compatibility with the canonical inclusions by uncurrying, before using
this result for general anima parameters.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.CoreOfFun
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.Evaluation 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
mappingInclusion : (C D : CAT) → MAP (Map C D) (Fun C D)
mappingInclusion C D = funCurry mapEval

module CoreOfFun (C D : CAT) where
  module U = Evaluation.At (funEval {C} {D}) One
  A = Core (Fun C D)

  uncurrying : MAP A (Map C D)
  uncurrying = mapPre (oneProduct-in C) ∘ U.forward

  uncurrying-isEquiv : IsEquiv uncurrying
  uncurrying-isEquiv = equiv-compose U.forward (mapPre (oneProduct-in C))
    (funUniversal C D One)
    (mapPre-isEquiv (oneProduct-in C) (oneProduct-in-isEquiv C))

  terminal-regroup :
    (Associativity.backward A One C ∘ productMap (id A) (oneProduct-in C)) =₁
    (productMap (product-unitʳ-inverse A) (id C))
  terminal-regroup =
    let k = productMap (id A) (oneProduct-in C)
        first = comp-unitˡ pr₁ ∙ pair-β₁ (id A ∘ pr₁) (oneProduct-in C ∘ pr₂)
        third = comp-unitˡ pr₂ ∙
          ((oneProduct-retraction C ▷ pr₂) ∙
          ((comp-assoc pr₂ (oneProduct-in C) pr₂) ⁻¹ ∙
          ((pr₂ ◁ pair-β₂ (id A ∘ pr₁) (oneProduct-in C ∘ pr₂)) ∙
            comp-assoc k pr₂ pr₂)))
        left-normal = pair-cong
          (pair-cong first (terminal-iso _ (terminate (A × C))) ∙ pair-pre pr₁ (pr₁ ∘ pr₂) k)
          third ∙ pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) k
        right-normal = pair-cong
          (pair-cong (comp-unitˡ pr₁) (terminal-iso _ _) ∙
            pair-pre (id A) (terminate A) pr₁)
          (comp-unitˡ pr₂)
    in right-normal ⁻¹ ∙ left-normal

  uncurrying-evaluation : (mapUncurry uncurrying) =₁
    (funUncurry (coreInclusion (Fun C D)))
  uncurrying-evaluation =
    (funUncurry-restrict mapEval (product-unitʳ-inverse A)) ⁻¹ ∙
    ((funUncurry mapEval ◁ terminal-regroup) ∙
    (comp-assoc (productMap (id A) (oneProduct-in C))
      (Associativity.backward A One C) (funUncurry mapEval) ∙
    ((mapCurry-β (map-isAn One (Fun C D)) U.evaluation
        ▷ productMap (id A) (oneProduct-in C)) ∙
      mapPre-uncurry (oneProduct-in C) U.forward)))

  inclusion-uncurrying : (mappingInclusion C D ∘ uncurrying) =₁
    (coreInclusion (Fun C D))
  inclusion-uncurrying = funReflect _ _
    (uncurrying-evaluation ∙
      ((funCurry-β mapEval ▷ productMap uncurrying (id C)) ∙
        funUncurry-restrict (mappingInclusion C D) uncurrying))

  comparison : MAP (Map C D) A
  comparison = IsEquiv.inverse uncurrying-isEquiv

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = equiv-inverse uncurrying-isEquiv

  inclusion-comparison : (coreInclusion (Fun C D) ∘ comparison) =₁
    (mappingInclusion C D)
  inclusion-comparison = comp-unitʳ (mappingInclusion C D) ∙
    ((mappingInclusion C D ◁ (IsEquiv.retractionIso uncurrying-isEquiv) ⁻¹) ∙
    (comp-assoc comparison uncurrying (mappingInclusion C D) ∙
      (inclusion-uncurrying ⁻¹ ▷ comparison)))

  comparison-on-maps : (X : CAT) → isAn X → IsEquiv (mapPost {C = X} comparison)
  comparison-on-maps X xAn = mapPost-isEquiv comparison comparison-isEquiv
```
