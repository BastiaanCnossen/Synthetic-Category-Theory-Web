# Restriction of relative functors, with its evaluation rule

Curry restriction of the universal family. Product separation then
identifies restriction of every family, including its triangle over the
base. When the argument is an equivalence, native restriction lifts the
universal family and reflects identifications; these two properties give
an inverse to the actual curried restriction functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
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
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.RestrictionEquivalences 𝒯 M ℱ P using (module Restriction)

module Precompose {A B C S : CAT} {a′ : MAP A S} {r : MAP B S}
  (f : MAP C S) (u : FunctorOver a′ r) where
  module Arg = Argument u
  Source = FunOver r f
  Target = FunOver a′ f
  source-family = universal r f
  target-family = universal a′ f
  restricted = compose-over source-family (Arg.family Source)

  functor : MAP Source Target
  functor = Curry.functor a′ f (FunctorLift.lift restricted) (FunctorLift.comparison restricted)

  maps : MAP (MapOver r f) (MapOver a′ f)
  maps = mapPost functor

  abstract
    evaluation-comparison : FunctorOverIso (family a′ f functor) restricted
    evaluation-comparison = curried-beta a′ f restricted

    family-comparison : {X : CAT} (F : MAP X Source) → FunctorOverIso
      (family a′ f (functor ∘ F)) (compose-over (family r f F) (Arg.family X))
    family-comparison {X} F = compose-iso-over
      (prewhisker-over (Arg.family X)
        (inverse-iso-over (evaluated-restriction F (pullbackCone (funPost f) (nameFun r)))))
      (compose-iso-over (inverse-iso-over (associator-over (Arg.family X) (parameter-over-functor r F) source-family))
        (compose-iso-over (postwhisker-over source-family (Arg.parameter F))
          (compose-iso-over (associator-over (parameter-over-functor a′ F) (Arg.family Source) source-family)
            (compose-iso-over (prewhisker-over (parameter-over-functor a′ F) evaluation-comparison)
              (family-composite a′ f F functor)))))

  module Equivalence (ee : IsEquiv (FunctorLift.lift u)) where
    argument-isEquiv : (X : CAT) → IsEquiv (FunctorLift.lift (Arg.family X))
    argument-isEquiv X = productMap-isEquiv (id X) (FunctorLift.lift u) (id-isEquiv X) ee
    module Native (X : CAT) = Restriction (r ∘ pr₂ {C = X}) f (Arg.family X) (argument-isEquiv X)
    module Lift = Native.Factor Target target-family

    inverse : MAP Target Source
    inverse = Curry.functor r f (FunctorLift.lift Lift.value) (FunctorLift.comparison Lift.value)

    abstract
      inverse-evaluation : FunctorOverIso (family r f inverse) Lift.value
      inverse-evaluation = curried-beta r f Lift.value

      right-inverse : (functor ∘ inverse) =₁ id Target
      right-inverse = reflect-family a′ f _ _
        (compose-iso-over (inverse-iso-over (family-identity a′ f))
          (compose-iso-over Lift.comparison
            (compose-iso-over (prewhisker-over (Arg.family Target) inverse-evaluation)
              (family-comparison inverse))))

      left-inverse : (inverse ∘ functor) =₁ id Source
      left-inverse = reflect-family r f _ _
        (Native.Reflect.comparison Source (family r f (inverse ∘ functor)) (family r f (id Source))
          (compose-iso-over (prewhisker-over (Arg.family Source) (inverse-iso-over (family-identity r f)))
            (compose-iso-over evaluation-comparison
              (compose-iso-over
                (evaluated-comparison (cone-action (pullbackCone (funPost f) (nameFun a′))
                  (comp-unitˡ functor ∙ ((right-inverse ▷ functor) ∙ (comp-assoc functor inverse functor) ⁻¹))))
                (inverse-iso-over (family-comparison (inverse ∘ functor)))))))

      functor-isEquiv : IsEquiv functor
      functor-isEquiv = record { inverse = inverse ; sectionIso = left-inverse ⁻¹ ; retractionIso = right-inverse ⁻¹ }

      maps-isEquiv : IsEquiv maps
      maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```
