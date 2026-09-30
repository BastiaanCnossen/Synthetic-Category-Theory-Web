# Verifying the proposed dependent pullback

The tested comparison is already an equivalence. To identify it with
uncurrying by the proposed evaluation, it suffices to compare the whole
evaluated cones and retain a relative comparison of their first legs.
The first leg recovers the base triangle of the lifted comparison.

This is a sufficient criterion, not yet the preservation theorem:
`Witness` records the remaining cone comparison, including its specified
matching equation. No comparison of the native triangle witnesses one
dimension higher is required at this final step.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.Section05.Currying.RelativeEvaluationFamilies as EvaluationFamilies

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackVerification
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneIso-compose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackReflection 𝒯 M ℱ P using (module Reflect)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackFamilies 𝒯 M ℱ P using (module FamiliesComparison)

module Verification {S T C D E : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) where
  module Candidate = Evaluation p ΠC ΠD ΠE u v using (evaluation; module Q; module R)

  module At {K : CAT} (k : MAP K T) where
    module Tested = FamiliesComparison p ΠC ΠD ΠE u v k
      using (evaluated-cone; module Compared; module Evaluated)
    module Raw = EvaluationFamilies.Evaluation 𝒯 M ℱ P p Candidate.R.projection
      Candidate.Q.projection Candidate.evaluation k using (functor; mapping-isEquiv)
    source = family Tested.Compared.k′ Candidate.R.projection Tested.Compared.forward
    target = family Tested.Compared.k′ Candidate.R.projection Raw.functor
    source-cone = conePre (FunctorLift.lift source)
      (pullbackCone (FunctorLift.lift u) (FunctorLift.lift v))
    target-cone = conePre (FunctorLift.lift target)
      (pullbackCone (FunctorLift.lift u) (FunctorLift.lift v))

    record Witness : Set m where
      field
        first : FunctorOverIso (compose-over Candidate.R.first source) (compose-over Candidate.R.first target)
        cones : ConeIso source-cone target-cone
        first-image : ConeIso.leftIso cones =₂ FunctorOverIso.underlying first

    module Verified (witness : Witness) where
      open Witness witness
      module Reflected = Reflect.Between u v source target first cones first-image using (comparison)

      opaque
        family-comparison : FunctorOverIso source target
        family-comparison = Reflected.comparison

        functor-comparison : Tested.Compared.forward =₁ Raw.functor
        functor-comparison = reflect-family Tested.Compared.k′ Candidate.R.projection
          Tested.Compared.forward Raw.functor family-comparison

        functor-isEquiv : IsEquiv Raw.functor
        functor-isEquiv = equiv-transport functor-comparison Tested.Compared.forward-isEquiv

        uncurrying-isEquiv : IsEquiv
          (EvaluationAlong.uncurrying p Candidate.R.projection Candidate.Q.projection Candidate.evaluation k)
        uncurrying-isEquiv = Raw.mapping-isEquiv functor-isEquiv

  verified : ({K : CAT} (k : MAP K T) → At.Witness k) →
    IsDependentProduct p Candidate.R.projection Candidate.Q.projection Candidate.evaluation
  verified witnesses = record { universal = λ k → At.Verified.uncurrying-isEquiv k (witnesses k) }
```
