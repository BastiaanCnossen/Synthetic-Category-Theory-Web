# Precomposition on hom fibers of coslices

Precomposition between coslices restricts to the specified precomposition
on hom categories. The comparison is reflected from the complete endpoint
cone, and its two images are retained for pullback pasting.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceFiberPrecomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-id)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; conePre; coneIso-compose; coneIso-inverse; IsPullback)
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceHomFibers as Fibers
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CoslicePrecompositionFamilies as Families
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifting
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
import SCT.VolumeI.Chapter01.Section06.Pasting.FiberSquares as FiberSquares
import SCT.VolumeI.Chapter04.Section03.CoslicePrecomposition as Original
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Laws.PullbackStructure P using (pullbackCone)

module Along {C : CAT} {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) (z : Obj-abs C) where
  private
    H = Hom C y z
    module Source = Fibers.At 𝒯 M ℱ P I y z
      using (inclusion; projection; expression-computation; square; square-isPullback)
    module Target = Fibers.At 𝒯 M ℱ P I x z using (inclusion; module Family; square; square-isPullback)
    module Action = At {C = C} {x = x} {y = y} e using (precompose; family)
    module Compute = Computation {C = C} {x = x} {y = y} e using (precompose)
    module Pre = Families.ForArrow 𝒯 M ℱ P I E S {C = C} {x = x} {y = y} e
      using (functor; module AtFamily)
    module First = Pre.AtFamily {Γ = H} Source.inclusion using (composite; specified-comparison; source-projection; target-projection; base-computation)
    module Last = Target.Family {Γ = H} (Action.precompose z) using (specified-comparison; source-projection; target-projection; base-computation)
    module Read = Reading.At 𝒯 M ℱ P I y using (read)
    module Lift = Lifting.At 𝒯 M ℱ P I x using (module Change)
    f = Action.family H
    g = Read.read {Γ = H} Source.inclusion
    source-id = idIso (const {P = H} x)
    middle-id = idIso (const {P = H} y)
    σ = Source.projection

    abstract
      expression-comparison : ExpressionIso (retarget-expression First.composite source-id σ)
        (hom-expression (Action.precompose z))
      expression-comparison = expressionIso-compose (expressionIso-inverse (Compute.precompose z))
        (expressionIso-compose
          (compose-expression-cong (retarget-id f) Source.expression-computation)
          (expressionIso-inverse (retarget-composition f g source-id middle-id σ)))
    module Changed = Lift.Change {Γ = H}
      {b = coslice-projection y ∘ Source.inclusion} {d = const {P = H} z}
      First.composite (hom-expression (Action.precompose z)) σ expression-comparison using (specified-comparison; source-projection; target-projection; base-computation)

  precompose = Pre.functor
  hom-precompose = Action.precompose z
  source-inclusion = Source.inclusion
  target-inclusion = Target.inclusion

  specified-comparison : ConeIso
    (conePre (precompose ∘ source-inclusion) (pullbackCone endpoints (pair (const x) (id C))))
    (conePre (target-inclusion ∘ hom-precompose) (pullbackCone endpoints (pair (const x) (id C))))
  specified-comparison = coneIso-compose (coneIso-inverse Last.specified-comparison)
    (coneIso-compose Changed.specified-comparison First.specified-comparison)
  private
    module Reflected = Reflection.Lift 𝒯 P
      {f = endpoints} {g = pair (const {P = C} x) (id C)}
      (precompose ∘ source-inclusion) (target-inclusion ∘ hom-precompose) specified-comparison
      using (lift; comparison-image; left-image; right-image)
  open Reflected public renaming (lift to comparison)

  square : Cone precompose target-inclusion H
  square = record { left = source-inclusion ; right = hom-precompose ; match = comparison }

  private
    module Ordinary = Original.Along 𝒯 M ℱ P I E S {C = C} {x = x} {y = y} e using (over-base)
    κ = FunctorLift.comparison Ordinary.over-base
    h = hom-precompose
    μ = terminal-iso (terminate (Hom C x z) ∘ h) (terminate H)
    module Pullback = FiberSquares.Along 𝒯 P precompose (coslice-projection x) (coslice-projection y)
      κ z Target.square Target.square-isPullback Source.square Source.square-isPullback h comparison μ
      using (projection-equation; module Compatible)
    first = ConeIso.rightIso First.specified-comparison
    changed = ConeIso.rightIso Changed.specified-comparison
    last = ConeIso.rightIso Last.specified-comparison
    β = Last.target-projection
    source-base = First.source-projection
    ψ = Last.source-projection

    abstract
      last-cancel : (ψ ∙ last ⁻¹) =₂ β
      last-cancel = cancel-right last β ∙ isoComp-cong (Last.base-computation ⁻¹) (idIso (last ⁻¹))

      base-normal : (ψ ∙ ConeIso.rightIso specified-comparison) =₂ (σ ∙ source-base)
      base-normal = isoComp-cong (idIso σ) First.base-computation ∙
        isoComp-assoc-at σ First.target-projection first ∙
        isoComp-cong Changed.base-computation (idIso first) ∙
        (isoComp-assoc-at β changed first) ⁻¹ ∙
        isoComp-cong last-cancel (idIso (changed ∙ first)) ∙
        (isoComp-assoc-at ψ (last ⁻¹) (changed ∙ first)) ⁻¹

      parameter-normal : ((z ◁ μ) ∙ Cone.match (conePre h Target.square)) =₂ ψ
      parameter-normal = (isoComp-assoc-at (z ◁ μ)
        (comp-assoc h (terminate (Hom C x z)) z)
        ((Cone.match Target.square ▷ h) ∙ (comp-assoc h target-inclusion (coslice-projection x)) ⁻¹)) ⁻¹

      fiber-compatibility : Pullback.projection-equation
      fiber-compatibility = base-normal ∙ isoComp-cong parameter-normal right-image

  abstract
    square-isPullback : IsPullback square
    square-isPullback = Pullback.Compatible.square-isPullback fiber-compatibility
```
