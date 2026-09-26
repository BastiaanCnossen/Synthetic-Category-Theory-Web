# Restriction under the exponential equivalence

Restricting the inner variable before uncurrying agrees with restricting
the corresponding product factor afterwards. The proof uncurries both
routes and compares their three product projections. This is the
endpoint calculation used in the slice pullback diagram.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter03.Section07.MappingCalculus.ExponentialRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.ExponentialLaw 𝒯 M ℱ using (module ExponentialLaw)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (pair-after)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (product-first; product-second)

module LastFactor (A B : CAT) {C D : CAT} (u : MAP C D) where
  left-change = productMap (id (A × B)) u
  right-change = productMap (id A) (productMap (id B) u)
  left-regroup = Associativity.backward A B C
  right-regroup = Associativity.backward A B D
  abstract
    right-first : (pr₁ ∘ right-change) =₁ pr₁
    right-first = comp-unitˡ pr₁ ∙ pair-β₁ (id A ∘ pr₁) (productMap (id B) u ∘ pr₂)
    right-second : ((pr₁ ∘ pr₂) ∘ right-change) =₁ (pr₁ ∘ pr₂)
    right-second = comp-unitˡ (pr₁ ∘ pr₂) ∙
      (product-first (id B) u pr₂ ∙
        ((pr₁ ◁ pair-β₂ (id A ∘ pr₁) (productMap (id B) u ∘ pr₂)) ∙ comp-assoc right-change pr₂ pr₁))
    right-third : ((pr₂ ∘ pr₂) ∘ right-change) =₁ (u ∘ (pr₂ ∘ pr₂))
    right-third = product-second (id B) u pr₂ ∙
      ((pr₂ ◁ pair-β₂ (id A ∘ pr₁) (productMap (id B) u ∘ pr₂)) ∙ comp-assoc right-change pr₂ pr₂)
    comparison : (left-change ∘ left-regroup) =₁ (right-regroup ∘ right-change)
    comparison =
      (pair-cong (pair-cong right-first right-second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) right-change)
        right-third ∙ pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) right-change) ⁻¹ ∙
      (pair-cong (comp-unitˡ (pair pr₁ (pr₁ ∘ pr₂))) (idIso (u ∘ (pr₂ ∘ pr₂))) ∙
        pair-after (id (A × B)) u (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂))

module Restriction (X E : CAT) {Y Z : CAT} (u : MAP Y Z) where
  module Before = ExponentialLaw X Z E
  module After = ExponentialLaw X Y E
  Source = Fun X (Fun Z E)
  inner = funPost {C = X} (funPre {D = E} u)
  product = productMap (id X) u
  module Regroup = LastFactor Source X u
  abstract
    double-restriction : funUncurry (funUncurry inner) =₁
      (Before.doubleEvaluation ∘ Regroup.left-change)
    double-restriction = funPre-uncurry u (funEval {X} {Fun Z E}) ∙
      funUncurry-cong (funPost-β (funPre {D = E} u))
    left-normal : funUncurry (After.forward ∘ inner) =₁
      (Before.doubleEvaluation ∘ (Regroup.right-regroup ∘ Regroup.right-change))
    left-normal = (Before.doubleEvaluation ◁ Regroup.comparison) ∙
      (comp-assoc Regroup.left-regroup Regroup.left-change Before.doubleEvaluation ∙
        ((double-restriction ▷ Regroup.left-regroup) ∙ After.forward-represents inner))
    right-normal : funUncurry (funPre product ∘ Before.forward) =₁
      (Before.doubleEvaluation ∘ (Regroup.right-regroup ∘ Regroup.right-change))
    right-normal = comp-assoc Regroup.right-change Regroup.right-regroup Before.doubleEvaluation ∙
      ((Before.forward-β ▷ Regroup.right-change) ∙ funPre-uncurry product Before.forward)
    comparison : (After.forward ∘ inner) =₁ (funPre product ∘ Before.forward)
    comparison = funReflect _ _ (right-normal ⁻¹ ∙ left-normal)
```
