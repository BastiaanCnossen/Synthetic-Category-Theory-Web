# Changing the parameter of an uncurried family

The two routes project to the same family over the original domain.
Uncurrying the projection triangle gives a comparison of these images.
Lift it through the reassociated product, prescribing its remaining
coordinate as well. Cancellation of the projection triangle then
recovers the comparison over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.UncurriedParameterComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (parameter-over-functor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Family)
open import SCT.VolumeI.Chapter03.Section05.Currying.UncurriedFamilyProjection 𝒯 M ℱ P using (module Project)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)
open import SCT.VolumeI.Chapter03.Section05.Currying.UncurriedTriangleComposition 𝒯 M ℱ P using (module Composite)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionReflection 𝒯 M ℱ P using (module Recover)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ReassociatedProductLifting 𝒯 P using (module Coordinates)
import SCT.VolumeI.Chapter03.Section05.Currying.FamilyProjection as Projection
module Proj = Projection 𝒯 M ℱ P

module Parameter {K S C B X Y : CAT} (r : MAP C B) (f : MAP K (Fun S B)) (σ : MAP Y X) where
  u = funUncurry f
  module FlatX = Family r f X using (insertion; regroup)
  module FlatY = Family r f Y using (insertion; regroup)
  module PX = Project r f X using (q; comparison)
  module PY = Project r f Y using (q; comparison)
  original = parameter-over-functor f σ
  uncurried = Uncurry.value S B original
  changed = parameter-over-functor u σ
  source = compose-over uncurried FlatY.insertion
  target = compose-over FlatX.insertion changed

  abstract
    projected-parameter : FunctorOverIso (compose-over PX.q uncurried) PY.q
    projected-parameter = compose-iso-over
      (Uncurry.Identification.comparison S B (Proj.Substitution.comparison f σ))
      (inverse-iso-over (Composite.comparison original (Proj.projection f X)))

    source-image : FunctorOverIso (compose-over PX.q source) (Proj.projection u Y)
    source-image = compose-iso-over PY.comparison
      (compose-iso-over (prewhisker-over FlatY.insertion projected-parameter)
        (inverse-iso-over (associator-over FlatY.insertion uncurried PX.q)))

    target-image : FunctorOverIso (compose-over PX.q target) (Proj.projection u Y)
    target-image = compose-iso-over (Proj.Substitution.comparison u σ)
      (compose-iso-over (prewhisker-over changed PX.comparison)
        (inverse-iso-over (associator-over changed FlatX.insertion PX.q)))

    projected-comparison : FunctorOverIso (compose-over PX.q source) (compose-over PX.q target)
    projected-comparison = compose-iso-over (inverse-iso-over target-image) source-image

  Q = productMap σ (id K)
  R = productMap Q (id S)
  Qflat = productMap σ (id (K × S))
  πX : MAP ((X × K) × S) (X × K)
  πX = pr₁
  πY : MAP ((Y × K) × S) (Y × K)
  πY = pr₁
  aX : MAP (X × K) X
  aX = pr₁
  aY : MAP (Y × K) Y
  aY = pr₁
  module Product = Coordinates X K S using (first; rest; module Lift)

  abstract
    first-step : (Product.first ∘ R) =₁ (σ ∘ (aY ∘ πY))
    first-step = comp-assoc πY aY σ ∙
      ((pair-β₁ (σ ∘ pr₁) (id K ∘ pr₂) ▷ πY) ∙
        ((comp-assoc πY Q aX) ⁻¹ ∙
          ((aX ◁ pair-β₁ (Q ∘ πY) (id S ∘ pr₂)) ∙ comp-assoc R πX aX)))

    source-first : (Product.first ∘ FunctorLift.lift source) =₁ (σ ∘ pr₁)
    source-first = (σ ◁ Associativity.backward-first Y K S) ∙
      (comp-assoc FlatY.regroup (aY ∘ πY) σ ∙
        ((first-step ▷ FlatY.regroup) ∙ (comp-assoc FlatY.regroup R Product.first) ⁻¹))

    target-first : (Product.first ∘ FunctorLift.lift target) =₁ (σ ∘ pr₁)
    target-first = pair-β₁ (σ ∘ pr₁) (id (K × S) ∘ pr₂) ∙
      ((Associativity.backward-first X K S ▷ Qflat) ∙
        (comp-assoc Qflat FlatX.regroup Product.first) ⁻¹)

  module Lifted = Product.Lift (FunctorLift.lift source) (FunctorLift.lift target)
    (target-first ⁻¹ ∙ source-first) (FunctorOverIso.underlying projected-comparison)
    using (comparison; rest-image)

  abstract
    comparison : FunctorOverIso source target
    comparison = Recover.comparison PX.q projected-comparison Lifted.comparison Lifted.rest-image
```
