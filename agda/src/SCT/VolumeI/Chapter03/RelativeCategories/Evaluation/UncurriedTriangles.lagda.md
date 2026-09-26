# Uncurrying triangles between structure functors

A triangle between maps into `Fun S B` uncurries to a triangle over
`B`, whose underlying functor is the original one times `S`.
Identifications retain their specified base compatibility. This is the
source-variable companion to native uncurrying of a target triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyProductFunctor as FamilyProduct

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily-absolute; productFamily-cong)

abstract
  restriction-natural : {Y X S B : CAT} (f : MAP X (Fun S B))
    {h k : MAP Y X} (α : h =₁ k) →
    (funUncurry-restrict f k ∙ funUncurryIso (f ◁ α)) =₂
      ((funUncurry f ◁ productMap-cong α (idIso (id S))) ∙ funUncurry-restrict f h)
  restriction-natural {S = S} f {h} {k} α = isoComp-cong
    (postWhisker (funUncurry f) ◁
      (productFamily-absolute α (idIso (id S)) ∙
        productFamily-cong (idIso α) (const-One (idIso (id S)))))
    (const-One (funUncurry-restrict f h)) ∙
    (uncurry-restrict-substitution f α ∙
      (isoComp-cong (const-One (funUncurry-restrict f k)) (uncurryFamily-absolute (f ◁ α))) ⁻¹)

module Uncurry (S B : CAT) where
  value : {X Y : CAT} {f : MAP X (Fun S B)} {g : MAP Y (Fun S B)} →
    FunctorOver f g → FunctorOver (funUncurry f) (funUncurry g)
  value {g = g} v = record { lift = productMap (FunctorLift.lift v) (id S)
    ; comparison = funUncurryIso (FunctorLift.comparison v) ∙
        (funUncurry-restrict g (FunctorLift.lift v)) ⁻¹ }

  module Identification {X Y : CAT} {f : MAP X (Fun S B)} {g : MAP Y (Fun S B)}
    {v w : FunctorOver f g} (Φ : FunctorOverIso v w) where
    h = FunctorLift.lift v
    k = FunctorLift.lift w
    α = FunctorOverIso.underlying Φ
    θ = FunctorLift.comparison v
    ψ = FunctorLift.comparison w
    b₀ = funUncurry-restrict g h
    b₁ = funUncurry-restrict g k
    first = funUncurry g ◁ productMap-cong α (idIso (id S))
    second = funUncurryIso (g ◁ α)
    final = idIso (funUncurry f)

    abstract
      matching : (funUncurryIso ψ ∙ second) =₂ (final ∙ funUncurryIso θ)
      matching = (isoComp-unitˡ-at (funUncurryIso θ)) ⁻¹ ∙
        ((funUncurry-isoMap _ _ ◁ FunctorOverIso.compatible Φ) ∙
          (funUncurryIso-comp ψ (g ◁ α)) ⁻¹)

      comparison : FunctorOverIso (value v) (value w)
      comparison = record { underlying = productMap-cong α (idIso (id S))
        ; compatible = isoComp-unitˡ-at (FunctorLift.comparison (value v)) ∙
            paste-iso-squares (b₀ ⁻¹) (b₁ ⁻¹) (funUncurryIso θ) (funUncurryIso ψ)
              first second final (move-square b₁ second first b₀ (restriction-natural g α)) matching }
```
