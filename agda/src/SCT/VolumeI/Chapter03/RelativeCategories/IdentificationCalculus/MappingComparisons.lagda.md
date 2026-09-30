# Comparing the relative mapping cospans

The mapping-anima/core equivalence commutes with postcomposition and
with the named structure functor. These are the two comparisons needed
to identify the core of the relative functor category with the mapping
fiber displayed in `def:Relative_Functor_Category_Global_Sections`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.MappingComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost; funPost-uncurry)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)

module Postcomposition (C : CAT) {D S : CAT} (g : MAP D S) where
  module Source = CoreOfFun C D using (uncurrying; uncurrying-evaluation)
  module Target = CoreOfFun C S using (uncurrying; uncurrying-evaluation)

  private
    left : mapUncurry (Target.uncurrying ∘ mapPost {C = One} (funPost {C = C} g)) =₁
        (g ∘ funUncurry (coreInclusion (Fun C D)))
    left = funPost-uncurry g (coreInclusion (Fun C D)) ∙
        (funUncurry-cong (coreInclusion-natural (funPost g)) ∙
          ((funUncurry-restrict (coreInclusion (Fun C S)) (mapPost (funPost g))) ⁻¹ ∙
            ((Target.uncurrying-evaluation ▷ productMap (mapPost (funPost g)) (id C)) ∙
              mapUncurry-restrict Target.uncurrying (mapPost (funPost g)))))
    right : mapUncurry (mapPost g ∘ Source.uncurrying) =₁
        (g ∘ funUncurry (coreInclusion (Fun C D)))
    right = (g ◁ Source.uncurrying-evaluation) ∙ mapPost-uncurry g Source.uncurrying

  comparison-image :
    mapUncurry (Target.uncurrying ∘ mapPost {C = One} (funPost {C = C} g)) =₁
    mapUncurry (mapPost g ∘ Source.uncurrying)
  comparison-image = right ⁻¹ ∙ left

  abstract
    comparison : (Target.uncurrying ∘ mapPost {C = One} (funPost {C = C} g)) =₁
      (mapPost g ∘ Source.uncurrying)
    comparison = mapReflect (core-isAn (Fun C D)) _ _ comparison-image

    comparison-β : mapUncurryIso comparison =₂ comparison-image
    comparison-β = mapReflect-β (core-isAn (Fun C D)) _ _ comparison-image

mapUncurry-constant-name : {X C S : CAT} (f : MAP C S) (u : MAP X One) →
  mapUncurry (nameMap f ∘ u) =₁ (f ∘ pr₂)
mapUncurry-constant-name {C = C} f u =
  (f ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (u ∘ pr₁) (id C ∘ pr₂))) ∙
    (comp-assoc (productMap u (id C)) pr₂ f ∙
      ((mapCurry-β one-isAn (f ∘ pr₂) ▷ productMap u (id C)) ∙
        mapUncurry-restrict (nameMap f) u))

module Named {C S : CAT} (f : MAP C S) where
  module Target = CoreOfFun C S using (uncurrying; uncurrying-evaluation)

  comparison-image :
    mapUncurry (Target.uncurrying ∘ mapPost {C = One} (nameFun f)) =₁
    mapUncurry (nameMap f ∘ coreInclusion One)
  comparison-image =
      ((mapUncurry-constant-name f (coreInclusion One)) ⁻¹ ∙
        (uncurry-constant-name f (coreInclusion One) ∙
          (funUncurry-cong (coreInclusion-natural (nameFun f)) ∙
            ((funUncurry-restrict (coreInclusion (Fun C S)) (mapPost (nameFun f))) ⁻¹ ∙
              ((Target.uncurrying-evaluation ▷ productMap (mapPost (nameFun f)) (id C)) ∙
                mapUncurry-restrict Target.uncurrying (mapPost (nameFun f)))))))

  abstract
    comparison : (Target.uncurrying ∘ mapPost {C = One} (nameFun f)) =₁
      (nameMap f ∘ coreInclusion One)
    comparison = mapReflect (core-isAn One) _ _ comparison-image

    comparison-β : mapUncurryIso comparison =₂ comparison-image
    comparison-β = mapReflect-β (core-isAn One) _ _ comparison-image
```
