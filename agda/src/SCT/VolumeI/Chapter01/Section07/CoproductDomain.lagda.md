# Functors out of a coproduct

For `lem:Functors_Out_Of_Coproduct`, test restriction on mapping animae.
Uncurrying, distributivity, and the coproduct axiom give the equivalence.
The two coproduct beta comparisons identify this composite with the
specified restriction functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.CoproductDomain
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M F

open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingTests 𝒯 M F
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)
import SCT.VolumeI.Chapter01.Section04.MappingProducts as MappingProducts
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯
  using (productMap-isEquiv; pair-after)

module CoproductDomain (C D E : CAT) where
  Source = Fun (C ⊔ D) E
  Target = Fun C E × Fun D E
  left = funPre {D = E} (in₁ {C} {D})
  right = funPre {D = E} (in₂ {C} {D})

  forward : MAP Source Target
  forward = pair left right

  module OnMaps (T : CAT) where
    open Distributivity T C D
    module TargetProduct = MappingProducts.ProductComparison 𝒯 M T (Fun C E) (Fun D E)
    module UC = Test T C E
    module UD = Test T D E
    module UCD = Test T (C ⊔ D) E
    leftIn = productMap (id T) (in₁ {C} {D})
    rightIn = productMap (id T) (in₂ {C} {D})

    restriction = coproductRestriction (T × C) (T × D) E ∘ mapPre distribute
    sourceComparison = restriction ∘ UCD.forward
    targetComparison = productMap UC.forward UD.forward ∘ TargetProduct.forward

    source-isEquiv : IsEquiv sourceComparison
    source-isEquiv = equiv-compose UCD.forward restriction UCD.forward-isEquiv
      (equiv-compose (mapPre distribute) (coproductRestriction (T × C) (T × D) E)
        (mapPre-isEquiv distribute distribute-isEquiv)
        (coproductRestriction-isEquiv (T × C) (T × D) E))

    target-isEquiv : IsEquiv targetComparison
    target-isEquiv = equiv-compose TargetProduct.forward (productMap UC.forward UD.forward)
      TargetProduct.forward-isEquiv
      (productMap-isEquiv UC.forward UD.forward UC.forward-isEquiv UD.forward-isEquiv)

    restriction-comparison : restriction =₁ (pair (mapPre leftIn) (mapPre rightIn))
    restriction-comparison = pair-cong
      (mapPre-cong (copair-β₁ leftIn rightIn) ∙ mapPre-comp in₁ distribute)
      (mapPre-cong (copair-β₂ leftIn rightIn) ∙ mapPre-comp in₂ distribute) ∙
      pair-pre (mapPre in₁) (mapPre in₂) (mapPre distribute)

    comparison-square : (targetComparison ∘ mapPost forward) =₁ sourceComparison
    comparison-square = (restriction-comparison ▷ UCD.forward) ⁻¹ ∙
      ((pair-pre (mapPre leftIn) (mapPre rightIn) UCD.forward) ⁻¹ ∙
      (pair-cong (precomposition T in₁) (precomposition T in₂) ∙
      (pair-after UC.forward UD.forward (mapPost left) (mapPost right) ∙
      ((productMap UC.forward UD.forward ◁ mapPost-pair left right) ∙
        comp-assoc (mapPost forward) TargetProduct.forward (productMap UC.forward UD.forward)))))

    comparison-isEquiv : IsEquiv (mapPost {C = T} forward)
    comparison-isEquiv = equiv-cancel-left (mapPost forward) targetComparison target-isEquiv
      (equiv-transport (comparison-square ⁻¹) source-isEquiv)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = post-tests-all forward OnMaps.comparison-isEquiv
```
