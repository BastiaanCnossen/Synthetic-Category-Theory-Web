# The whole cone of the proposed evaluation

Evaluate the universal family and restrict the cone used to construct
the proposed evaluation. These operations give the same cone, including
its specified matching. The proof uses the identity-family comparison,
associativity of restriction, and the full pullback beta comparison.

Thus the remaining preservation proof can compare with this restricted
cone directly. This does not yet identify it with the tested equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.Section05.Currying.RelativeEvaluationFamilies as EvaluationFamilies

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackEvaluationCone
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (universal; family)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentEvaluationLegs 𝒯 M ℱ P using (module IdentityFamily)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)

module EvaluatedCone {S T C D E : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) where
  module Candidate = Evaluation p ΠC ΠD ΠE u v using (evaluation; module Q; module R; module Lifted)

  module At {K : CAT} (k : MAP K T) where
    module Raw = EvaluationFamilies.Evaluation 𝒯 M ℱ P p Candidate.R.projection
      Candidate.Q.projection Candidate.evaluation k using (functor; module At)
    module Identity = IdentityFamily p Candidate.R.projection Candidate.Q.projection
      Candidate.evaluation k using (comparison)
    X = FunOver k Candidate.Q.projection
    module Parameter = Raw.At X using (inclusion)
    k′ : MAP (Pullback k p) S
    k′ = pullback₂
    ε = FunctorLift.lift Candidate.evaluation
    changed = FunctorLift.lift (Change.functor p (universal k Candidate.Q.projection))
    inclusion = FunctorLift.lift Parameter.inclusion
    defining = pullbackCone (FunctorLift.lift u) (FunctorLift.lift v)

    actual = conePre (FunctorLift.lift (family k′ Candidate.R.projection Raw.functor)) defining
    restricted = conePre inclusion (conePre changed Candidate.Lifted.cone)

    opaque
      comparison : ConeIso actual restricted
      comparison = coneIso-compose
        (coneIso-pre inclusion (coneIso-pre changed Candidate.Lifted.cone-comparison))
        (coneIso-compose
          (coneIso-pre inclusion (coneIso-inverse (conePre-assoc changed ε defining)))
          (coneIso-compose
            (coneIso-inverse (conePre-assoc inclusion (ε ∘ changed) defining))
            (cone-action defining (FunctorOverIso.underlying Identity.comparison))))
```
