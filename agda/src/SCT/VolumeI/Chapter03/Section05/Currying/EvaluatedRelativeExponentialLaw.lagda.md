# The relative exponential law with its evaluation rule

Uncurry the universal family of relative functors and reassociate its
parameter product. Relative currying gives the comparison functor.
The inverse is obtained by the inverse construction on families.
Their native inverse comparisons, together with parameter substitution,
prove equivalence and the computation on every family.

The separate pullback proof in `RelativeExponentialLaw` establishes the
same categorical equivalence. This presentation supplies the evaluation
rule needed to identify a dependent product's specified uncurrying map.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedRelativeExponentialLaw
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M using (mapPost; mapPost-isEquiv)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Family)
open import SCT.VolumeI.Chapter03.Section05.Currying.UncurriedFamilySubstitution 𝒯 M ℱ P using (module Substitution)

module Law {K S C B : CAT} (r : MAP C B) (f : MAP K (Fun S B)) where
  u = funUncurry f
  Source = FunOver f (funPost r)
  Target = FunOver u r
  source-family = universal f (funPost r)
  target-family = universal u r
  to-family = Family.value r f Source source-family
  from-family = Family.Recovery.backward r f Target target-family

  functor : MAP Source Target
  functor = Curry.functor u r (FunctorLift.lift to-family) (FunctorLift.comparison to-family)
  inverse : MAP Target Source
  inverse = Curry.functor f (funPost r) (FunctorLift.lift from-family) (FunctorLift.comparison from-family)

  abstract
    evaluation-comparison : FunctorOverIso (family u r functor) to-family
    evaluation-comparison = curried-beta u r to-family

    inverse-evaluation : FunctorOverIso (family f (funPost r) inverse) from-family
    inverse-evaluation = curried-beta f (funPost r) from-family

    family-comparison : {X : CAT} (F : MAP X Source) →
      FunctorOverIso (family u r (functor ∘ F)) (Family.value r f X (family f (funPost r) F))
    family-comparison {X} F = compose-iso-over
      (Family.identification r f X (inverse-iso-over (evaluated-restriction F (pullbackCone (funPost (funPost r)) (nameFun f)))))
      (compose-iso-over (inverse-iso-over (Substitution.comparison r f F source-family))
        (compose-iso-over (prewhisker-over (parameter-over-functor u F) evaluation-comparison)
          (family-composite u r F functor)))

    right-inverse : (functor ∘ inverse) =₁ id Target
    right-inverse = reflect-family u r _ _
      (compose-iso-over (inverse-iso-over (family-identity u r))
        (compose-iso-over (Family.Recovery.comparison r f Target target-family)
          (compose-iso-over (Family.identification r f Target inverse-evaluation) (family-comparison inverse))))

    left-inverse : (inverse ∘ functor) =₁ id Source
    left-inverse = reflect-family f (funPost r) _ _
      (Family.reflect r f Source
        (compose-iso-over (Family.identification r f Source (inverse-iso-over (family-identity f (funPost r))))
          (compose-iso-over evaluation-comparison
            (compose-iso-over
              (family-identification u r
                (comp-unitˡ functor ∙ ((right-inverse ▷ functor) ∙ (comp-assoc functor inverse functor) ⁻¹)))
              (inverse-iso-over (family-comparison (inverse ∘ functor)))))))

    functor-isEquiv : IsEquiv functor
    functor-isEquiv = record { inverse = inverse ; sectionIso = left-inverse ⁻¹ ; retractionIso = right-inverse ⁻¹ }

  maps : MAP (MapOver f (funPost r)) (MapOver u r)
  maps = mapPost functor
  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```
