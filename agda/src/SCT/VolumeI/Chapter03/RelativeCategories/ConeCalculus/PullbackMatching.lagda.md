# The specified matching after relative postcomposition

Evaluate the two composite families and apply the relative pullback
matching. Lifting this native comparison constructs the commutativity
identification in the relative functor square. We retain its evaluated
image, including the complete encoded triangle. The underlying image
compares this particular square with the cartesian forgetful squares;
the encoded image also survives native base change.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackMatching
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyLifting 𝒯 M ℱ P using (action)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.CoherentRelativeFamilyLifting 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

module Matching {K C D E S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} {h : MAP E S} (u : FunctorOver f h) (v : FunctorOver g h) where
  module R = RelativePullback u v
  module U = Postcompose k u
  module V = Postcompose k v
  module First = Postcompose k R.first
  module Second = Postcompose k R.second
  source = U.functor ∘ First.functor
  target = V.functor ∘ Second.functor
  abstract
    left-family : FunctorOverIso (family k h source)
      (compose-over (compose-over u R.first) (universal k R.projection))
    left-family = compose-iso-over (inverse-iso-over (associator-over (universal k R.projection) R.first u))
      (compose-iso-over (postwhisker-over u First.family-comparison)
        (postcompose-family k u First.functor))
    right-family : FunctorOverIso (family k h target)
      (compose-over (compose-over v R.second) (universal k R.projection))
    right-family = compose-iso-over (inverse-iso-over (associator-over (universal k R.projection) R.second v))
      (compose-iso-over (postwhisker-over v Second.family-comparison)
        (postcompose-family k v Second.functor))
    native-comparison : FunctorOverIso (family k h source) (family k h target)
    native-comparison = compose-iso-over (inverse-iso-over right-family)
      (compose-iso-over (prewhisker-over (universal k R.projection) R.match-over) left-family)
    left-family-underlying : FunctorOverIso.underlying left-family =₂
      ((comp-assoc (FunctorLift.lift (universal k R.projection)) R.first-map R.left-map) ⁻¹ ∙
        ((R.left-map ◁ FunctorOverIso.underlying First.family-comparison) ∙
          FunctorOverIso.underlying (postcompose-family k u First.functor)))
    left-family-underlying = idIso _
    right-family-underlying : FunctorOverIso.underlying right-family =₂
      ((comp-assoc (FunctorLift.lift (universal k R.projection)) R.second-map R.right-map) ⁻¹ ∙
        ((R.right-map ◁ FunctorOverIso.underlying Second.family-comparison) ∙
          FunctorOverIso.underlying (postcompose-family k v Second.functor)))
    right-family-underlying = idIso _
    native-comparison-underlying : FunctorOverIso.underlying native-comparison =₂
      ((FunctorOverIso.underlying right-family) ⁻¹ ∙
        ((R.matching ▷ FunctorLift.lift (universal k R.projection)) ∙
          FunctorOverIso.underlying left-family))
    native-comparison-underlying = idIso _
  module Lifted = Families k h source target using (action; Result; result; result-image)
  lifted : Lifted.Result native-comparison
  lifted = Lifted.result native-comparison
  matching : source =₁ target
  matching = Lifted.Result.comparison lifted
  abstract
    evaluated-computation : FunctorOverIso₂ (Lifted.action matching) native-comparison
    evaluated-computation = Lifted.Result.full-image lifted
    evaluated-image : FunctorOverIso.underlying (action k h matching) =₂
      FunctorOverIso.underlying native-comparison
    evaluated-image = Lifted.result-image native-comparison lifted
  opaque
    base-change-computation : {B : CAT} (p : MAP B S) →
      FunctorOverIso₂
        (Change.Identification.comparison p (Lifted.action matching))
        (Change.Identification.comparison p native-comparison)
    base-change-computation p = Change.higher-identification-image p
      {u = family k h source} {v = family k h target}
      {Φ = Lifted.action matching} {Ψ = native-comparison} evaluated-computation

    base-change-image : {B : CAT} (p : MAP B S) →
      FunctorOverIso.underlying (Change.Identification.comparison p (Lifted.action matching)) =₂
      FunctorOverIso.underlying (Change.Identification.comparison p native-comparison)
    base-change-image p = Change.encoded-identification-image p (Lifted.Result.encoded-image lifted)
  cone : Cone U.functor V.functor (FunOver k R.projection)
  cone = record { left = First.functor ; right = Second.functor ; match = matching }
```
