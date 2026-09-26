# Base change of the relative functor category

For `con:Base_Change_Of_Functor_Categories`, apply pullback functoriality
to the universal family of triangles over the base. Currying the
resulting family gives the functor on relative functor categories.
Taking cores gives its action on relative mapping animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Evaluation; module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointComputations 𝒯 M ℱ P using (module Family)

open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (module CurriedTriangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (EvaluatedCone)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies 𝒯 M ℱ P using (module CurriedFamily)

open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (universal)
import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.PulledFamilies as PulledFamilies

module BaseChange {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  X = FunOver f g
  C′ = Pullback f p
  D′ = Pullback g p
  f′ : MAP C′ S
  f′ = pullback₂
  g′ : MAP D′ S
  g′ = pullback₂

  module UniversalFamily = PulledFamilies.Change.At 𝒯 M ℱ P
    {C = C} {D = D} {S = S} {T = T} p f g {X = X} (universal f g)
    using (R; cone; pulled)

  parameter : MAP (X × C′) (X × C)
  parameter = UniversalFamily.R

  cone : Cone g p (X × C′)
  cone = UniversalFamily.cone

  evaluated : FunctorOver (f′ ∘ pr₂ {C = X}) g′
  evaluated = UniversalFamily.pulled

  evaluation : MAP (X × C′) D′
  evaluation = FunctorLift.lift evaluated

  evaluation-over : (g′ ∘ evaluation) =₁ (f′ ∘ pr₂)
  evaluation-over = FunctorLift.comparison evaluated

  module Curried = Curry f′ g′ evaluation evaluation-over using (functor; comparison; evaluation)

  abstract
    functor : MAP (FunOver f g) (FunOver f′ g′)
    functor = Curried.functor

    maps : MAP (MapOver f g) (MapOver f′ g′)
    maps = mapPost functor

    maps-as-core : maps =₁ mapPost functor
    maps-as-core = idIso maps

    family-comparison : FunctorOverIso
      (EvaluatedCone (conePre functor (pullbackCone (funPost g′) (nameFun f′)))) evaluated
    family-comparison = record
      { underlying = CurriedTriangle.evaluation-with-image f′ g′ evaluation evaluation-over
      ; compatible = CurriedTriangle.native-beta f′ g′ evaluation evaluation-over }

    evaluation-comparison :
      ConeIso (conePre (funUncurry (Over.forget f′ g′ ∘ functor)) (pullbackCone g p)) cone
    evaluation-comparison = coneIso-compose (pullbackLift-β cone)
      (cone-action (pullbackCone g p) Curried.evaluation)

    on-points-cone : (x : Obj-abs (MapOver f g)) →
      ConeIso (conePre (FunctorLift.lift (Over.decode-over f′ g′ (maps ∘ x))) (pullbackCone g p))
        (conePre (Family.parameter f′ g′ functor x) cone)
    on-points-cone x = coneIso-compose
      (coneIso-pre (Family.parameter f′ g′ functor x) evaluation-comparison)
      (coneIso-compose
        (coneIso-inverse (conePre-assoc (Family.parameter f′ g′ functor x)
          (funUncurry (Over.forget f′ g′ ∘ functor)) (pullbackCone g p)))
        (cone-action (pullbackCone g p) (Family.comparison f′ g′ functor x)))

    on-points-over : (x : Obj-abs (MapOver f g)) →
      FunctorOverIso (Over.decode-over f′ g′ (maps ∘ x))
        (compose-over evaluated (CurriedFamily.Evaluated.parameter f′ g′ evaluated x))
    on-points-over x = CurriedFamily.comparison f′ g′ evaluated x

```

`on-points-over` retains the native triangle when evaluating the curried
pullback family at a relative mapping point.

`evaluation-comparison` compares the entire evaluated pullback cone.
In particular, base change retains the original triangle's specified
commutativity identification when constructing the new functor.
