# Restricting the induced join functor to its two summands

The join evaluation is inverse to the canonical boundary comparison.
Its defining dependent-product computation therefore identifies the
base change of the induced join functor with the prescribed coproduct
functor. Projecting gives its restrictions to both summands.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinFunctorBoundary
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M hiding (_⋆_)
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I using (weakened-boundary)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_; join-in₁; join-in₂)
import SCT.VolumeI.Chapter03.Section06.JoinFunctoriality as Functoriality
open Functoriality 𝒯 M ℱ B P U I J using (module Presentation; joinMap)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J using (dataJoin; height; inclusion; boundary-isEquiv)

module BoundaryInverse (C D : CAT) where
  p = terminate C
  q = terminate D
  module Boundary = BoundaryComparison dataJoin p q using (functor; comparison; evaluation-underlying)
  module Source = Presentation C D using (dependent-product)
  comparison = Boundary.functor
  evaluation = FunctorLift.lift (DependentProduct.evaluation Source.dependent-product)
  abstract
    evaluation-image : evaluation =₁ IsEquiv.inverse (boundary-isEquiv p q)
    evaluation-image = Boundary.evaluation-underlying (boundary-isEquiv p q) ∙ comp-unitˡ _
    evaluation-isEquiv : IsEquiv evaluation
    evaluation-isEquiv = equiv-transport (evaluation-image ⁻¹) (equiv-inverse (boundary-isEquiv p q))
    left-inverse : (evaluation ∘ comparison) =₁ id (C ⊔ D)
    left-inverse = (IsEquiv.sectionIso (boundary-isEquiv p q)) ⁻¹ ∙ (evaluation-image ▷ comparison)
    first-image : (pullback₁ ∘ comparison) =₁ inclusion p q
    first-image = ConeIso.leftIso Boundary.comparison

module Restriction {C D C′ D′ : CAT} (f : MAP C C′) (g : MAP D D′) where
  module Chosen = Functoriality.Action 𝒯 M ℱ B P U I J f g using (over; boundary-over)
  module Source = Presentation C D using (projection; dependent-product)
  module Target = Presentation C′ D′ using (projection; dependent-product)
  module S = BoundaryInverse C D using (comparison; evaluation; left-inverse; first-image)
  module T = BoundaryInverse C′ D′ using (comparison; evaluation; evaluation-isEquiv; left-inverse; first-image)
  b = weakened-boundary One
  u = joinMap f g
  v = FunctorLift.lift Chosen.boundary-over
  changed = FunctorLift.lift (Change.functor b Chosen.over)
  β = FunctorOverIso.underlying
    (Action.evaluation-comparison b Source.projection Target.projection
      Source.dependent-product Target.dependent-product Chosen.boundary-over)
  abstract
    source-reduction : (T.evaluation ∘ (changed ∘ S.comparison)) =₁ v
    source-reduction = comp-unitʳ v ∙ ((v ◁ S.left-inverse) ∙
      (comp-assoc S.comparison S.evaluation v ∙
        ((β ▷ S.comparison) ∙ (comp-assoc S.comparison changed T.evaluation) ⁻¹)))
    target-reduction : (T.evaluation ∘ (T.comparison ∘ v)) =₁ v
    target-reduction = comp-unitˡ v ∙ ((T.left-inverse ▷ v) ∙
      (comp-assoc v T.comparison T.evaluation) ⁻¹)
    boundary-base-change : (changed ∘ S.comparison) =₁ (T.comparison ∘ v)
    boundary-base-change = equiv-reflect T.evaluation-isEquiv _ _
      (target-reduction ⁻¹ ∙ source-reduction)

    source-projection : (pullback₁ ∘ (changed ∘ S.comparison)) =₁
      (u ∘ inclusion (terminate C) (terminate D))
    source-projection = (u ◁ S.first-image) ∙
      (comp-assoc S.comparison pullback₁ u ∙
        ((pullbackLift-β₁ (Change.cone b Chosen.over) ▷ S.comparison) ∙
          (comp-assoc S.comparison changed pullback₁) ⁻¹))
    target-projection : (pullback₁ ∘ (T.comparison ∘ v)) =₁
      (inclusion (terminate C′) (terminate D′) ∘ v)
    target-projection = (T.first-image ▷ v) ∙ (comp-assoc v T.comparison pullback₁) ⁻¹
    boundary-comparison : (u ∘ inclusion (terminate C) (terminate D)) =₁
      (inclusion (terminate C′) (terminate D′) ∘ coproductMap f g)
    boundary-comparison = target-projection ∙ ((pullback₁ ◁ boundary-base-change) ∙ source-projection ⁻¹)

    first-comparison : (u ∘ join-in₁ {C} {D}) =₁ (join-in₁ {C′} {D′} ∘ f)
    first-comparison = (comp-assoc f in₁ (inclusion (terminate C′) (terminate D′))) ⁻¹ ∙
      ((inclusion (terminate C′) (terminate D′) ◁ copair-β₁ (in₁ ∘ f) (in₂ ∘ g)) ∙
        (comp-assoc in₁ (coproductMap f g) (inclusion (terminate C′) (terminate D′)) ∙
          ((boundary-comparison ▷ in₁) ∙
            (comp-assoc in₁ (inclusion (terminate C) (terminate D)) u) ⁻¹)))
    second-comparison : (u ∘ join-in₂ {C} {D}) =₁ (join-in₂ {C′} {D′} ∘ g)
    second-comparison = (comp-assoc g in₂ (inclusion (terminate C′) (terminate D′))) ⁻¹ ∙
      ((inclusion (terminate C′) (terminate D′) ◁ copair-β₂ (in₁ ∘ f) (in₂ ∘ g)) ∙
        (comp-assoc in₂ (coproductMap f g) (inclusion (terminate C′) (terminate D′)) ∙
          ((boundary-comparison ▷ in₂) ∙
            (comp-assoc in₂ (inclusion (terminate C) (terminate D)) u) ⁻¹)))
```
