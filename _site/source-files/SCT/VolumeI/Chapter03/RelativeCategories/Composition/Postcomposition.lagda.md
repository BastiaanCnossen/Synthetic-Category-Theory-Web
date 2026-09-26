# Postcomposition over a base

A functor over the base acts on relative functor categories by
postcomposing their universal families. Its specified triangle is used
in the resulting triangle, so the construction also determines the
action on relative mapping animae. The native point computation and its
naming comparison below retain the entire triangle over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Evaluation; module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointComputations 𝒯 M ℱ P using (module Postcomposition)

open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone; conePre)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (module CurriedTriangle)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies 𝒯 M ℱ P
  using (universal-point; module CurriedFamily)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingComparisons 𝒯 M ℱ P using (module Triangles)
open Pullbacks.PullbackStructure P using (pullbackCone)

module Postcompose {B C D S : CAT} (f : MAP B S) {g : MAP C S} {h : MAP D S}
  (u : FunctorOver g h) where
  k = FunctorLift.lift u

  evaluation : MAP (FunOver f g × B) D
  evaluation = k ∘ Evaluation.evaluate f g

  over : (h ∘ evaluation) =₁ (f ∘ pr₂)
  over = Evaluation.over f g ∙
    ((FunctorLift.comparison u ▷ Evaluation.evaluate f g) ∙
      (comp-assoc (Evaluation.evaluate f g) k h) ⁻¹)

  universal-evaluation : FunctorOver (f ∘ pr₂ {C = FunOver f g}) g
  universal-evaluation = EvaluatedCone (pullbackCone (funPost g) (nameFun f))

  evaluated : FunctorOver (f ∘ pr₂ {C = FunOver f g}) h
  evaluated = compose-over u universal-evaluation

  module Curried = Curry f h evaluation over using (functor; comparison; evaluation)

  abstract
    functor : MAP (FunOver f g) (FunOver f h)
    functor = Curried.functor

    maps : MAP (MapOver f g) (MapOver f h)
    maps = mapPost functor

    maps-as-core : maps =₁ mapPost functor
    maps-as-core = idIso maps

    evaluation-comparison : funUncurry (Over.forget f h ∘ functor) =₁ evaluation
    evaluation-comparison = Curried.evaluation

    family-comparison : FunctorOverIso
      (EvaluatedCone (conePre functor (pullbackCone (funPost h) (nameFun f)))) evaluated
    family-comparison = record
      { underlying = CurriedTriangle.evaluation-with-image f h evaluation over
      ; compatible = CurriedTriangle.native-beta f h evaluation over }

    on-points : (x : Obj-abs (MapOver f g)) →
      FunctorLift.lift (Over.decode-over f h (maps ∘ x)) =₁
        (k ∘ FunctorLift.lift (Over.decode-over f g x))
    on-points = Postcomposition.comparison f g h k functor evaluation-comparison

    on-points-over : (x : Obj-abs (MapOver f g)) →
      FunctorOverIso (Over.decode-over f h (maps ∘ x))
        (compose-over u (Over.decode-over f g x))
    on-points-over x = compose-iso-over (postwhisker-over u (inverse-iso-over (universal-point f g x)))
      (compose-iso-over
        (associator-over (CurriedFamily.Evaluated.parameter f h evaluated x) universal-evaluation u)
        (CurriedFamily.comparison f h evaluated x))

    on-named-points : (v : FunctorOver f g) →
      (maps ∘ Over.name-over f g v) =₁ Over.name-over f h (compose-over u v)
    on-named-points v =
      Triangles.Identification.identification f h
        (Over.decode-over f h (maps ∘ Over.name-over f g v)) (compose-over u v)
        (compose-iso-over (postwhisker-over u (Triangles.decode-name-native f g v))
          (on-points-over (Over.name-over f g v))) ∙
        (Over.name-decode-over f h (maps ∘ Over.name-over f g v)) ⁻¹

```
