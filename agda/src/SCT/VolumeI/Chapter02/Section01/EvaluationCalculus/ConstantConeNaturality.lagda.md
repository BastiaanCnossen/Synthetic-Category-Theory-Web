# Constant diagrams of a whole cone

The constant-diagram map of cospans carries a cone to the restriction
of its mapped cone along the constant-diagram functor. Its matching
comparison follows from the chosen uncurrying computations, not from
agreement of the two legs alone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantConeNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (transport-square)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (uncurryCone)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingNormalization 𝒯 M ℱ
  using (endpoints-iterated)
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantDiagramNaturality as Constants
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantConeFrames as Frames
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantConeComparison as ConstantComparison
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones as Coordinates
import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeReflection as Reflection

module At {C D B Γ : CAT} {f : MAP C B} {g : MAP D B}
  (A : CAT) (t : Cone f g Γ) where
  module Constant = Constants.At 𝒯 M ℱ A using (comparison; module Naturality; module Post)
  module Coordinate = Coordinates.Coordinate 𝒯 f g (funPost f) (funPost g)
    (constantDiagram A C) (constantDiagram A D) (constantDiagram A B)
    (Constant.Post.value f) (Constant.Post.value g)
    using (read; left-normal; right-normal)
  module ConstantTarget = ConstantComparison.At 𝒯 M ℱ P A t
    using (restricted; evaluated-restriction)
  l = Cone.left t
  r = Cone.right t
  τ = Cone.match t
  l₀ = Coordinate.left-normal l
  r₀ = Coordinate.right-normal r
  q₀ = constantDiagram A B ◁ τ
  left-leg = Constant.comparison l
  right-leg = Constant.comparison r
  Ef = funPost-uncurry f (constantDiagram A C ∘ l)
  Eg = funPost-uncurry g (constantDiagram A D ∘ r)
  L = Ef ∙ funUncurryIso l₀
  R = Eg ∙ funUncurryIso r₀
  al = comp-assoc (pr₁ {C = Γ} {D = A}) l f
  ar = comp-assoc (pr₁ {C = Γ} {D = A}) r g
  source = uncurryCone (Coordinate.read t)
  target = conePre (pr₁ {C = Γ} {D = A}) t
  rawSource = changeEndpoints L R (funUncurryIso q₀)

  abstract
    source-normal : Cone.match source =₂ rawSource
    source-normal = endpoints-iterated (funUncurryIso l₀) (funUncurryIso r₀)
        Ef Eg (funUncurryIso q₀) ∙
      isoComp-cong (idIso Eg)
        (isoComp-cong
          (isoComp-cong (idIso (funUncurryIso r₀))
            (isoComp-cong (idIso (funUncurryIso q₀)) (funUncurryIso-inverse l₀) ∙
              funUncurryIso-comp q₀ (l₀ ⁻¹)) ∙
            funUncurryIso-comp r₀ (q₀ ∙ l₀ ⁻¹))
          (idIso (Ef ⁻¹)))

    raw-square : (Cone.match target ∙ (f ◁ left-leg)) =₂ ((g ◁ right-leg) ∙ rawSource)
    raw-square = transport-square L al R ar (funUncurryIso q₀) (τ ▷ pr₁)
      (Constant.comparison (f ∘ l)) (Constant.comparison (g ∘ r))
      (f ◁ left-leg) (g ◁ right-leg)
      (Frames.At.value 𝒯 M ℱ A f l ⁻¹) (Frames.At.value 𝒯 M ℱ A g r ⁻¹)
      (Constant.Naturality.value τ ⁻¹)

    uncurried : ConeIso source target
    uncurried = record { leftIso = left-leg ; rightIso = right-leg
      ; compatible = isoComp-cong (idIso (g ◁ right-leg)) (source-normal ⁻¹) ∙ raw-square }

    value : ConeIso (Coordinate.read t) ConstantTarget.restricted
    value = Reflection.ReflectCone.comparison 𝒯 M ℱ (Coordinate.read t) ConstantTarget.restricted
      (coneIso-compose (coneIso-inverse ConstantTarget.evaluated-restriction) uncurried)
```
