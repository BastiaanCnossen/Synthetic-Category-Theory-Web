# Composition for uncurried structure triangles

The compositor is the standard comparison for product with the identity.
Its compatibility with the base triangle follows from successive
substitution for uncurrying. Thus source-variable uncurrying respects
composition with the supplied finite coherence data.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.Section05.Currying.UncurriedTriangleComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingSubstitution 𝒯 M ℱ using (module Iteration)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (reassociateFour)

module Composite {X Y Z S B : CAT}
  {f : MAP X (Fun S B)} {g : MAP Y (Fun S B)} {k : MAP Z (Fun S B)}
  (u : FunctorOver f g) (v : FunctorOver g k) where
  h = FunctorLift.lift u
  j = FunctorLift.lift v
  θ = FunctorLift.comparison u
  ψ = FunctorLift.comparison v
  H = productMap h (id S)
  J = productMap j (id S)
  κ = slice-comparison {C = S} j h
  β = comp-assoc h j k
  ρ = funUncurry-restrict k (j ∘ h)
  μ = funUncurryIso β
  ν = funUncurry-restrict (k ∘ j) h
  δ = funUncurry-restrict k j ▷ H
  ε = comp-assoc H J (funUncurry k)
  γ = funUncurry k ◁ κ
  n = funUncurry-restrict g h
  s = funUncurryIso (ψ ▷ h)
  t = funUncurryIso ψ ▷ H
  Θ = funUncurryIso θ
  tail = δ ⁻¹ ∙ (ε ⁻¹ ∙ γ ⁻¹)
  source = Uncurry.value S B (compose-over v u)
  target = compose-over (Uncurry.value S B v) (Uncurry.value S B u)

  abstract
    tail-comparison : (μ ⁻¹ ∙ ρ ⁻¹) =₂ (ν ⁻¹ ∙ tail)
    tail-comparison = isoComp-assoc-at (ν ⁻¹) (δ ⁻¹) (ε ⁻¹ ∙ γ ⁻¹) ∙
      (isoComp-cong (inverse-composite δ ν) (idIso (ε ⁻¹ ∙ γ ⁻¹)) ∙
        (isoComp-assoc-at ((δ ∙ ν) ⁻¹) (ε ⁻¹) (γ ⁻¹) ∙
          (isoComp-cong (inverse-composite ε (δ ∙ ν)) (idIso (γ ⁻¹)) ∙
            (inverse-composite γ (ε ∙ (δ ∙ ν)) ∙
              ((＝-inv ◁ Iteration.coherence k j h) ∙ (inverse-composite ρ μ) ⁻¹)))))

    source-normal : FunctorLift.comparison source =₂ (Θ ∙ (s ∙ (μ ⁻¹ ∙ ρ ⁻¹)))
    source-normal = isoComp-cong (idIso Θ) (isoComp-assoc-at s (μ ⁻¹) (ρ ⁻¹)) ∙
      (isoComp-assoc-at Θ (s ∙ μ ⁻¹) (ρ ⁻¹) ∙
        isoComp-cong
          (isoComp-cong (idIso Θ)
            (isoComp-cong (idIso s) (funUncurryIso-inverse β) ∙ funUncurryIso-comp (ψ ▷ h) (β ⁻¹)) ∙
              funUncurryIso-comp θ ((ψ ▷ h) ∙ β ⁻¹))
          (idIso (ρ ⁻¹)))

    restricted-triangle : (FunctorLift.comparison (Uncurry.value S B v) ▷ H) =₂ (t ∙ δ ⁻¹)
    restricted-triangle = isoComp-cong (idIso t) (pre-inverse (funUncurry-restrict k j) H) ∙
      preWhisker-isoComp-at (funUncurryIso ψ) ((funUncurry-restrict k j) ⁻¹) H

    target-normal : (FunctorLift.comparison target ∙ (funUncurry k ◁ κ ⁻¹)) =₂
      (Θ ∙ ((n ⁻¹ ∙ t) ∙ tail))
    target-normal = reassociateFour Θ (n ⁻¹) t tail ∙
      (isoComp-cong (idIso (Θ ∙ n ⁻¹)) (isoComp-assoc-at t (δ ⁻¹) (ε ⁻¹ ∙ γ ⁻¹)) ∙
        (isoComp-cong (idIso (Θ ∙ n ⁻¹)) (isoComp-assoc-at (t ∙ δ ⁻¹) (ε ⁻¹) (γ ⁻¹)) ∙
          (isoComp-assoc-at (Θ ∙ n ⁻¹) ((t ∙ δ ⁻¹) ∙ ε ⁻¹) (γ ⁻¹) ∙
            isoComp-cong (isoComp-cong (idIso (Θ ∙ n ⁻¹))
              (isoComp-cong restricted-triangle (idIso (ε ⁻¹)))) (post-inverse (funUncurry k) κ))))

    comparison : FunctorOverIso source target
    comparison = record { underlying = κ ⁻¹
      ; compatible = source-normal ⁻¹ ∙
          (isoComp-cong (idIso Θ) (isoComp-cong (idIso s) (tail-comparison ⁻¹)) ∙
            (isoComp-cong (idIso Θ) (isoComp-assoc-at s (ν ⁻¹) tail) ∙
              (isoComp-cong (idIso Θ)
                (isoComp-cong (move-square n s t ν (funUncurry-restrict-inputs ψ h)) (idIso tail)) ∙ target-normal))) }
```
