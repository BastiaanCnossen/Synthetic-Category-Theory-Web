# The pullback-target comparison with its evaluation rule

Curry projection of the universal native family to obtain the comparison
of relative functor categories. Curry pullback lifting to obtain its
inverse. The native inverse comparisons and substitution law identify
the two composite families with the identity families, so reflection
proves the equivalence of the actual functors.

Unlike the separate pullback-pasting proof in `RelativePullbackTargets`,
this presentation directly exports the computation on arbitrary families.
It is used to identify the relative internal functor category's literal
evaluation map.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)

module PullbackTarget {A C D S : CAT} (f : MAP C S) (g : MAP D S) (r : MAP A C) where
  module Native = Families f g r
  π = Native.projection
  Source = FunOver r π
  Target = FunOver (f ∘ r) g
  source-family = universal r π
  target-family = universal (f ∘ r) g
  to-family = Native.forward source-family
  from-family = Native.backward target-family

  functor : MAP Source Target
  functor = Curry.functor (f ∘ r) g (FunctorLift.lift to-family) (FunctorLift.comparison to-family)
  inverse : MAP Target Source
  inverse = Curry.functor r π (FunctorLift.lift from-family) (FunctorLift.comparison from-family)

  abstract
    evaluation-comparison : FunctorOverIso (family (f ∘ r) g functor) to-family
    evaluation-comparison = curried-beta (f ∘ r) g to-family

    inverse-evaluation : FunctorOverIso (family r π inverse) from-family
    inverse-evaluation = curried-beta r π from-family

    family-comparison : {X : CAT} (F : MAP X Source) →
      FunctorOverIso (family (f ∘ r) g (functor ∘ F)) (Native.forward (family r π F))
    family-comparison F = compose-iso-over
      (Native.forward-identification (inverse-iso-over (evaluated-restriction F (pullbackCone (funPost π) (nameFun r)))))
      (compose-iso-over (inverse-iso-over (Native.Substitution.comparison F source-family))
        (compose-iso-over (prewhisker-over (parameter-over-functor (f ∘ r) F) evaluation-comparison)
          (family-composite (f ∘ r) g F functor)))

    right-inverse : (functor ∘ inverse) =₁ id Target
    right-inverse = reflect-family (f ∘ r) g _ _
      (compose-iso-over (inverse-iso-over (family-identity (f ∘ r) g))
        (compose-iso-over (Native.forward-backward target-family)
          (compose-iso-over (Native.forward-identification inverse-evaluation) (family-comparison inverse))))

    left-inverse : (inverse ∘ functor) =₁ id Source
    left-inverse = reflect-family r π _ _
      (Native.reflect (family r π (inverse ∘ functor)) (family r π (id Source))
        (compose-iso-over (Native.forward-identification (inverse-iso-over (family-identity r π)))
          (compose-iso-over evaluation-comparison
            (compose-iso-over
              (evaluated-comparison (cone-action (pullbackCone (funPost g) (nameFun (f ∘ r)))
                (comp-unitˡ functor ∙ ((right-inverse ▷ functor) ∙ (comp-assoc functor inverse functor) ⁻¹))))
              (inverse-iso-over (family-comparison (inverse ∘ functor)))))))

    functor-isEquiv : IsEquiv functor
    functor-isEquiv = record { inverse = inverse ; sectionIso = left-inverse ⁻¹ ; retractionIso = right-inverse ⁻¹ }

  maps : MAP (MapOver r π) (MapOver (f ∘ r) g)
  maps = mapPost functor

  maps-isEquiv : IsEquiv maps
  maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```
