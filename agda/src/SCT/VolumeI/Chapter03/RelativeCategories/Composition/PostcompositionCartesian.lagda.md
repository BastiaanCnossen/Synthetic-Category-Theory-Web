# The cartesian square for relative postcomposition

Ordinary postcomposition, equipped with its evaluated triangle, acts on
the defining relative fiber. Its cartesian square is the native
base-change square. Comparing the whole evaluated families identifies
that fiber map with the previously defined relative postcomposition.
Transporting the square along this identification gives the claimed
pullback for the actual implementation.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionCartesian
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family; universal; postcompose-family; postcompose-family-underlying)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyLifting 𝒯 M ℱ P using (module Identification)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (evaluated-comparison)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Squares 𝒯 M ℱ P using (module Cartesian)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.FunctorPostTriangles 𝒯 M ℱ P using (module Post)
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedSquareRestriction as SquareRestriction
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

module Postcomposition {K C D S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} (u : FunctorOver f g) where
  private
    module Higher = Post K u using (triangle; module OnCone)
    module Pullback = Cartesian (nameFun k) Higher.triangle using (square; square-isPullback)
    module Actual = Postcompose k u using (functor; family-comparison)
  source = pullbackCone (funPost f) (nameFun k)
  target = pullbackCone (funPost g) (nameFun k)
  acted = Change.cone (nameFun k) Higher.triangle
  fiber-map = pullbackLift acted

  abstract
    evaluated : FunctorOverIso (family k g fiber-map) (compose-over u (universal k f))
    evaluated = compose-iso-over (Higher.OnCone.comparison k source)
      (evaluated-comparison (pullbackLift-β acted))
  family-comparison = compose-iso-over (inverse-iso-over Actual.family-comparison) evaluated
  private
    module Lifted = Identification k g fiber-map Actual.functor family-comparison
  abstract
    comparison : fiber-map =₁ Actual.functor
    comparison = Lifted.comparison
    forgetful-image : (Over.forget k g ◁ comparison) =₂
      funIsoReflect (Over.forget k g ∘ fiber-map) (Over.forget k g ∘ Actual.functor)
        (FunctorOverIso.underlying family-comparison)
    forgetful-image = Lifted.Lifted.left-image

  square : Cone (funPost (FunctorLift.lift u)) (Over.forget k g) (FunOver k f)
  square = record { left = Over.forget k f ; right = Actual.functor
    ; match = (Over.forget k g ◁ comparison) ∙ Cone.match Pullback.square }
  abstract
    evaluated-matching : funUncurryIso (Cone.match square) =₂
      ((FunctorOverIso.underlying Actual.family-comparison) ⁻¹ ∙
        FunctorOverIso.underlying (Higher.OnCone.comparison k source))
    evaluated-matching =
      let b = funUncurryIso (ConeIso.leftIso (pullbackLift-β acted))
          d = FunctorOverIso.underlying Actual.family-comparison ⁻¹
          e = FunctorOverIso.underlying (Higher.OnCone.comparison k source)
      in cancel-right b (d ∙ e) ∙
        (isoComp-cong ((isoComp-assoc-at d e b) ⁻¹ ∙ Lifted.image)
          (funUncurryIso-inverse (ConeIso.leftIso (pullbackLift-β acted))) ∙
          funUncurryIso-comp (Over.forget k g ◁ comparison) (Cone.match Pullback.square))
    evaluated-matching-normal : funUncurryIso (Cone.match square) =₂
      ((FunctorOverIso.underlying Actual.family-comparison) ⁻¹ ∙
        funPost-uncurry (FunctorLift.lift u) (Over.forget k f))
    evaluated-matching-normal =
      isoComp-cong (idIso (FunctorOverIso.underlying Actual.family-comparison ⁻¹))
        (Higher.OnCone.comparison-underlying k source) ∙ evaluated-matching
    square-comparison : ConeIso Pullback.square square
    square-comparison = record { leftIso = idIso (Over.forget k f) ; rightIso = comparison
      ; compatible = isoComp-unitʳ-at (Cone.match square) ∙
          isoComp-cong (idIso (Cone.match square))
            (postWhisker-idIso (funPost (FunctorLift.lift u)) (Over.forget k f)) }
    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant square-comparison Pullback.square-isPullback
  module Restricted {X : CAT} (F : MAP X (FunOver k f)) where
    restricted = conePre F square
    β = FunctorOverIso.underlying (postcompose-family k u F)
    private
      module Normalize = SquareRestriction.Restrict 𝒯 M ℱ P (FunctorLift.lift u)
        (Over.forget k f) (Over.forget k g) Actual.functor (Cone.match square)
        (FunctorOverIso.underlying Actual.family-comparison) evaluated-matching-normal F
        using (normalized)
    abstract
      evaluation : (β ∙ funUncurryIso (Cone.match restricted)) =₂
        funPost-uncurry (FunctorLift.lift u) (Over.forget k f ∘ F)
      evaluation = Normalize.normalized ∙
        isoComp-cong (postcompose-family-underlying k u F)
          (idIso (funUncurryIso (Cone.match restricted)))
      family-comparison-image : β =₂
        (funPost-uncurry (FunctorLift.lift u) (Over.forget k f ∘ F) ∙
          (funUncurryIso (Cone.match restricted)) ⁻¹)
      family-comparison-image = isoComp-cong evaluation
        (idIso ((funUncurryIso (Cone.match restricted)) ⁻¹)) ∙
        (cancel-right (funUncurryIso (Cone.match restricted)) β) ⁻¹
```
