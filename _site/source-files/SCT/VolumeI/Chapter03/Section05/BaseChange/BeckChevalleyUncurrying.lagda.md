# The square of relative uncurrying functors

The two pullback-target comparisons and restriction along the pasting
equivalence identify the pulled evaluation with the original one. This
module proves the square on entire relative functor categories by
comparing their universal families. Taking cores will give the square
of mapping animae used in the universal-property argument.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyUncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.EvaluatedBaseChange 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeSubstitution 𝒯 M ℱ P using (module Substitution)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection 𝒯 M ℱ P using (module Identification)
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyEvaluation 𝒯 M ℱ P using (module Pulled)

module Square {S T S′ T′ C D : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (square-isPullback : IsPullback square) (g : MAP D T) (f : MAP C S)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) where
  module PulledEval = Pulled p b square square-isPullback g f ε using (module Dom; module At; pulled)
  open PulledEval.Dom using (h; p′; t)
  pulled = PulledEval.pulled

  module At {K : CAT} (k : MAP K T′) where
    X = FunOver k t
    u = universal k t
    module Families = PulledEval.At {K = K} {X = X} k u using (module Geometric; module Target; common; old-evaluated; comparison)
    module Geometry = Families.Geometric using (module Parameters; module New; module Old; argument)
    open Geometry.Parameters using (rN; rO)
    open Geometry using (argument)
    module A = PullbackTarget b g k using (functor; maps; maps-isEquiv; evaluation-comparison)
    module B = PullbackTarget h f rN using (functor; maps; maps-isEquiv; family-comparison)
    module Restrict = Precompose f Geometry.Parameters.flatten-over using (functor; maps; family-comparison; module Equivalence)
    module NewBC = BaseChange p′ k t using (f′; g′; functor; maps; maps-as-core; family-comparison)
    module NewPost = Postcompose rN pulled using (functor; maps; maps-as-core)
    module OldBC = BaseChange p (b ∘ k) g using (f′; g′; functor; maps; maps-as-core; family-comparison)
    module OldPost = Postcompose rO ε using (functor; maps; maps-as-core)
    left = B.functor ∘ (NewPost.functor ∘ NewBC.functor)
    right = Restrict.functor ∘ (OldPost.functor ∘ (OldBC.functor ∘ A.functor))

    abstract
      restriction-maps-isEquiv : IsEquiv Restrict.maps
      restriction-maps-isEquiv = Restrict.Equivalence.maps-isEquiv Geometry.Parameters.Nest.flatten-isEquiv

      new-family : FunctorOverIso (family NewBC.f′ NewBC.g′ NewBC.functor) Geometry.New.pulled
      new-family = compose-iso-over (Evaluation.same-family p′ k t) NewBC.family-comparison

      left-evaluated : FunctorOverIso
        (family rN (pullback₂ {f = f} {h}) (NewPost.functor ∘ NewBC.functor))
        (compose-over pulled Geometry.New.pulled)
      left-evaluated = compose-iso-over (postwhisker-over pulled new-family)
        (postcompose-family rN pulled NewBC.functor)

      left-family : FunctorOverIso (family (h ∘ rN) f left) Families.common
      left-family = compose-iso-over Families.comparison
        (compose-iso-over (Families.Target.forward-identification left-evaluated)
          (B.family-comparison (NewPost.functor ∘ NewBC.functor)))

      old-base-family : FunctorOverIso (family OldBC.f′ OldBC.g′ (OldBC.functor ∘ A.functor))
        Geometry.Old.pulled
      old-base-family = compose-iso-over (Identification.comparison p (b ∘ k) g A.evaluation-comparison)
        (Substitution.family-comparison p (b ∘ k) g A.functor)

      old-family : FunctorOverIso (family rO f (OldPost.functor ∘ (OldBC.functor ∘ A.functor)))
        Families.old-evaluated
      old-family = compose-iso-over (postwhisker-over ε old-base-family)
        (postcompose-family rO ε (OldBC.functor ∘ A.functor))

      right-family : FunctorOverIso (family (h ∘ rN) f right) Families.common
      right-family = compose-iso-over (prewhisker-over argument old-family)
        (Restrict.family-comparison (OldPost.functor ∘ (OldBC.functor ∘ A.functor)))

      comparison : left =₁ right
      comparison = reflect-family (h ∘ rN) f left right
        (compose-iso-over (inverse-iso-over right-family) left-family)
```
