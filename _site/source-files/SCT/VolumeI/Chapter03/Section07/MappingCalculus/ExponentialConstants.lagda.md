# Constant families under the exponential equivalence

Uncurrying a family constant in the inner variable is restriction along
the first projection. Uncurrying a fixed functor is restriction along
the second projection. These two calculations identify the lower map
in the functor-category pullback defining a slice.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section07.MappingCalculus.ExponentialConstants
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.ExponentialLaw 𝒯 M ℱ using (module ExponentialLaw)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)

module Projection (X Y C : CAT) where
  module Exponential = ExponentialLaw X Y C
  Source = Fun X C
  constant : MAP C (Fun Y C)
  constant = funCurry pr₁
  inner = funPost {C = X} constant
  regroup = Associativity.backward Source X Y
  evaluation = funEval {X} {C}
  coordinates : MAP (Source × (X × Y)) (Source × X)
  coordinates = pair pr₁ (pr₁ ∘ pr₂)
  abstract
    double-constant : funUncurry (funUncurry inner) =₁ (evaluation ∘ pr₁)
    double-constant = pair-β₁ (evaluation ∘ pr₁) (id Y ∘ pr₂) ∙
      ((funCurry-β (pr₁ {C} {Y}) ▷ productMap evaluation (id Y)) ∙
        (funUncurry-restrict constant evaluation ∙ funUncurry-cong (funPost-β constant)))
    left-normal : funUncurry (Exponential.forward ∘ inner) =₁ (evaluation ∘ coordinates)
    left-normal = (evaluation ◁ pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) ∙
      (comp-assoc regroup pr₁ evaluation ∙
        ((double-constant ▷ regroup) ∙ Exponential.forward-represents inner))
    right-normal : funUncurry (funPre {D = C} (pr₁ {X} {Y})) =₁ (evaluation ∘ coordinates)
    right-normal = (evaluation ◁ pair-cong (comp-unitˡ pr₁) (idIso (pr₁ ∘ pr₂))) ∙ funPre-β pr₁
    comparison : (Exponential.forward ∘ inner) =₁ funPre (pr₁ {X} {Y})
    comparison = funReflect _ _ (right-normal ⁻¹ ∙ left-normal)

module Fixed (X : CAT) {Y C : CAT} (ψ : MAP Y C) where
  module Exponential = ExponentialLaw X Y C
  Source = Fun X C
  constant : MAP C (Fun Y C)
  constant = const (nameFun ψ)
  inner = funPost {C = X} constant
  regroup = Associativity.backward Source X Y
  abstract
    double-constant : funUncurry (funUncurry inner) =₁ (ψ ∘ pr₂)
    double-constant = uncurry-constant-name ψ (terminate C ∘ funEval {X} {C}) ∙
      (funUncurry-cong (comp-assoc (funEval {X} {C}) (terminate C) (nameFun ψ)) ∙
        funUncurry-cong (funPost-β constant))
    left-normal : funUncurry (Exponential.forward ∘ inner) =₁ (ψ ∘ (pr₂ ∘ pr₂))
    left-normal = (ψ ◁ Associativity.backward-third Source X Y) ∙
      (comp-assoc regroup pr₂ ψ ∙ ((double-constant ▷ regroup) ∙ Exponential.forward-represents inner))
    right-normal : funUncurry (funPre (pr₂ {X} {Y}) ∘ const {P = Source} (nameFun ψ)) =₁
      (ψ ∘ (pr₂ ∘ pr₂))
    right-normal = (ψ ◁ pair-β₂ (id Source ∘ pr₁) (pr₂ ∘ pr₂)) ∙
      (comp-assoc (productMap (id Source) (pr₂ {X} {Y})) pr₂ ψ ∙
        ((uncurry-constant-name ψ (terminate Source) ▷ productMap (id Source) (pr₂ {X} {Y})) ∙
          funPre-uncurry (pr₂ {X} {Y}) (const (nameFun ψ))))
    comparison : (Exponential.forward ∘ inner) =₁
      (funPre (pr₂ {X} {Y}) ∘ const {P = Source} (nameFun ψ))
    comparison = funReflect _ _ (right-normal ⁻¹ ∙ left-normal)
```
