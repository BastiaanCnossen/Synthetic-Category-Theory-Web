# Base change computes on arbitrary relative families

Projection after base change is the restriction functor along the first
pullback projection. Compare their universal families and reflect to
obtain an identification of the actual functors. Substitution then gives
the base-change computation for every parameter category, since the
pullback-target comparison reflects native identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.EvaluatedBaseChange 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)

module Substitution {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  module BC = BaseChange p f g
  module Native = Change p f g
  module Target = PullbackTarget p g BC.f′
  module Restrict = Precompose g Native.projection
  module Evaluated = Evaluation p f g

  abstract
    projected-functor : (Target.functor ∘ BC.functor) =₁ Restrict.functor
    projected-functor = reflect-family (p ∘ BC.f′) g _ _
      (compose-iso-over (inverse-iso-over Restrict.evaluation-comparison)
        (compose-iso-over Evaluated.projection-comparison
          (compose-iso-over (Native.Project.forward-identification BC.family-comparison)
            (Target.family-comparison BC.functor))))

    family-comparison : {X : CAT} (F : MAP X (FunOver f g)) → FunctorOverIso
      (family BC.f′ BC.g′ (BC.functor ∘ F)) (Native.At.pulled (family f g F))
    family-comparison F = Native.Project.reflect _ _
      (compose-iso-over (inverse-iso-over (Native.At.projection-comparison (family f g F)))
        (compose-iso-over (Restrict.family-comparison F)
          (compose-iso-over (family-identification (p ∘ BC.f′) g (projected-functor ▷ F))
            (compose-iso-over (family-identification (p ∘ BC.f′) g ((comp-assoc F BC.functor Target.functor) ⁻¹))
              (inverse-iso-over (Target.family-comparison (BC.functor ∘ F)))))))
```
