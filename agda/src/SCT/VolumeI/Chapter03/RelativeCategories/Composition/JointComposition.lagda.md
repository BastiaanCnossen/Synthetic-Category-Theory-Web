# Joint composition of relative functor families

Compose the two universal relative families and curry the result. This
defines one composition functor on the product of the two relative
functor categories. Its evaluation on any common parameter is compared
with composition of the corresponding families, retaining the native
triangle over the base.

The construction is a joint choice. Agreement with separately chosen
composition operations requires an explicit comparison.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeRestriction as Restriction

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.JointComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P
  using (module Retained; module Identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
  using (family; family-composite; family-identification; curried-beta)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P
  using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
  using (parameter-over-functor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P
  using (reflect-family)
open Restriction 𝒯 M ℱ P using (module CompositeFamilyRestriction)

-- A joint operation constructed by currying the common-parameter family.
-- No agreement with old, separately chosen composition operations is asserted.
module Joint {A B C S : CAT} (f : MAP A S) (g : MAP B S) (h : MAP C S) where
  parameter = FunOver g h × FunOver f g
  inner : FunctorOver (f ∘ pr₂ {C = parameter}) g
  inner = family f g pr₂
  outer : FunctorOver (g ∘ pr₂ {C = parameter}) h
  outer = family g h pr₁
  module Inner = Retained f g inner
  composite = compose-over outer Inner.over

  functor : MAP parameter (FunOver f h)
  functor = Curry.functor f h (FunctorLift.lift composite) (FunctorLift.comparison composite)

  module At {X : CAT} (F : MAP X (FunOver f g)) (G : MAP X (FunOver g h)) where
    σ = pair G F
    paramA = parameter-over-functor f σ
    paramB = parameter-over-functor g σ
    restricted-inner = compose-over inner paramA
    restricted-outer = compose-over outer paramB
    actual-inner = family f g F
    actual-outer = family g h G
    module ActualInner = Retained f g actual-inner
    module RestrictedInner = Retained f g restricted-inner
    module Restricted = CompositeFamilyRestriction f g h σ inner outer
    actual = compose-over actual-outer ActualInner.over

    opaque
      inner-comparison : FunctorOverIso restricted-inner actual-inner
      inner-comparison = compose-iso-over (family-identification f g (pair-β₂ G F))
        (inverse-iso-over (family-composite f g σ pr₂))

      outer-comparison : FunctorOverIso restricted-outer actual-outer
      outer-comparison = compose-iso-over (family-identification g h (pair-β₁ G F))
        (inverse-iso-over (family-composite g h σ pr₁))

      normalized : FunctorOverIso Restricted.source actual
      normalized = compose-iso-over
        (postwhisker-over actual-outer
          (Identification.comparison f g restricted-inner actual-inner inner-comparison))
        (prewhisker-over RestrictedInner.over outer-comparison)

      evaluation : FunctorOverIso (family f h (functor ∘ σ)) actual
      evaluation = compose-iso-over normalized
        (compose-iso-over (inverse-iso-over Restricted.comparison)
          (compose-iso-over (prewhisker-over paramA (curried-beta f h composite))
            (family-composite f h σ functor)))

    actual-name = Curry.functor f h (FunctorLift.lift actual) (FunctorLift.comparison actual)

    opaque
      name-comparison : (functor ∘ σ) =₁ actual-name
      name-comparison = reflect-family f h (functor ∘ σ) actual-name
        (compose-iso-over (inverse-iso-over (curried-beta f h actual)) evaluation)
```
