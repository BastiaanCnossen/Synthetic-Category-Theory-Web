# The remaining matching equation for dependent pullbacks

Both projections of the tested equivalence agree with the projections of
actual evaluation. The comparisons below are relative identifications,
so in particular the first one retains the triangle over the base.

The remaining input is their ordinary matching equation. Once it is
proved, `verified` supplies the universal property for the proposed
dependent product, using the specified uncurrying map. This module does
not supply or assume that input.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackMatchingCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentEvaluationLegs 𝒯 M ℱ P using (module Projection)
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackVerification 𝒯 M ℱ P using (module Verification)

module Criterion {S T C D E : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) where
  module Candidate = Evaluation p ΠC ΠD ΠE u v using (evaluation; module Q; module R; module Lifted)
  module Check = Verification p ΠC ΠD ΠE u v using (module At; verified)
  module First = Projection p f (DependentProduct.projection ΠC) Candidate.R.projection Candidate.Q.projection
    (DependentProduct.evaluation ΠC) Candidate.evaluation Candidate.R.first Candidate.Q.first
    Candidate.Lifted.first-comparison using (module At)
  module Second = Projection p g (DependentProduct.projection ΠD) Candidate.R.projection Candidate.Q.projection
    (DependentProduct.evaluation ΠD) Candidate.evaluation Candidate.R.second Candidate.Q.second
    Candidate.Lifted.second-comparison using (module At)

  module At {K : CAT} (k : MAP K T) where
    module V = Check.At k using (source; target; source-cone; target-cone; Witness; module Tested; module Verified)
    forward = V.Tested.Compared.forward
    module Left = First.At.Compared k forward (ConeIso.leftIso V.Tested.Compared.forward-cone)
      using (comparison)
    module Right = Second.At.Compared k forward (ConeIso.rightIso V.Tested.Compared.forward-cone)
      using (comparison)

    first : FunctorOverIso (compose-over Candidate.R.first V.source) (compose-over Candidate.R.first V.target)
    first = Left.comparison
    second : FunctorOverIso (compose-over Candidate.R.second V.source) (compose-over Candidate.R.second V.target)
    second = Right.comparison
    α = FunctorOverIso.underlying first
    β = FunctorOverIso.underlying second

    Matching : Set m
    Matching = (Cone.match V.target-cone ∙ (FunctorLift.lift u ◁ α)) =₂
      ((FunctorLift.lift v ◁ β) ∙ Cone.match V.source-cone)

    comparison : Matching → ConeIso V.source-cone V.target-cone
    comparison matching = record { leftIso = α ; rightIso = β ; compatible = matching }

    opaque
      witness : Matching → V.Witness
      witness matching = record
        { first = first
        ; cones = comparison matching
        ; first-image = idIso α }

  verified : ({K : CAT} (k : MAP K T) → At.Matching k) →
    IsDependentProduct p Candidate.R.projection Candidate.Q.projection Candidate.evaluation
  verified matching = Check.verified (λ k → At.witness k (matching k))
```
