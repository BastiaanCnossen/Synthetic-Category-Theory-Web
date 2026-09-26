# Uncurrying a triangle in the source category

Postcompose a triangle with a family of functors, then uncurry it.
The restriction comparisons identify this operation with adjoining the
identity on the argument category. The equation retains both structure
triangles and is the naturality needed for fiberwise evaluation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedBaseTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P using (postbase)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry; restriction-natural)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingSubstitution 𝒯 M ℱ using (module Iteration)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Triangle {K G T S B : CAT} (F : MAP T (Fun S B))
  {k : MAP K T} {g : MAP G T} (u : FunctorOver k g) where
  h = FunctorLift.lift u
  θ = FunctorLift.comparison u
  H = productMap h (id S)
  G′ = productMap g (id S)
  K′ = productMap k (id S)
  A = comp-assoc h g F
  A′ = comp-assoc H G′ (funUncurry F)
  κ = slice-comparison {C = S} g h
  τ = productMap-cong θ (idIso (id S))
  η = funUncurry-restrict F k
  α = funUncurry-restrict F g
  ρ = funUncurry-restrict F (g ∘ h)
  ν = funUncurry-restrict (F ∘ g) h
  μ = funUncurryIso A
  χ = funUncurryIso (F ◁ θ)
  J = funUncurry F ◁ τ
  L = funUncurry F ◁ κ
  δ = α ▷ H
  original = Uncurry.value S B (postbase F u)
  triangle = (J ∙ L) ∙ A′
  value : FunctorOver (funUncurry F ∘ K′) (funUncurry F ∘ G′)
  value = record { lift = H ; comparison = triangle }

  abstract
    expanded : (η ∙ funUncurryIso (FunctorLift.comparison (postbase F u))) =₂
      (triangle ∙ (δ ∙ ν))
    expanded = (isoComp-assoc-at (J ∙ L) A′ (δ ∙ ν)) ⁻¹ ∙
      ((isoComp-assoc-at J L (A′ ∙ (δ ∙ ν))) ⁻¹ ∙
        (isoComp-cong (idIso J) (Iteration.coherence F g h) ∙
          (isoComp-assoc-at J ρ μ ∙
            (isoComp-cong (restriction-natural F θ) (idIso μ) ∙
              ((isoComp-assoc-at η χ μ) ⁻¹ ∙
                isoComp-cong (idIso η) (funUncurryIso-comp (F ◁ θ) A))))))

    comparison : (η ∙ FunctorLift.comparison original) =₂ (triangle ∙ δ)
    comparison = isoComp-cong (idIso triangle) (cancel-right ν δ) ∙
      (isoComp-assoc-at triangle (δ ∙ ν) (ν ⁻¹) ∙
        (isoComp-cong expanded (idIso (ν ⁻¹)) ∙
          (isoComp-assoc-at η (funUncurryIso (FunctorLift.comparison (postbase F u))) (ν ⁻¹)) ⁻¹))
```
