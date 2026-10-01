# Relative functors over a coproduct base

A relative functor over a coproduct is a pair of relative functors on
its two inverse images. Decompose its source by coproduct universality,
restrict to the summands, and use the two specified pullback squares
for its target. Taking cores gives the corresponding product of mapping
animae. All base triangles are retained in these constructions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter03.RelativeCategories.CoproductCalculus.CoproductDescent
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Universality 𝒯 M B P
open CoproductUniversality U
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B using (coproductMap; copair; copair-inclusions)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.CoproductCalculus.UniversalCoproductDescent 𝒯 M B P U using (module Cover)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section04.MappingProducts 𝒯 M using (module ProductComparison)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Coproducts 𝒯 M ℱ P B using (module Sum)
open import SCT.VolumeI.Chapter03.RelativeCategories.CoproductCalculus.CoproductMapping 𝒯 M ℱ P B U using () renaming (module Restriction to Split)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionEquivalences 𝒯 M ℱ P using (module Post)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)

module Separated {C D A Γ₀ Γ₁ S X : CAT}
  (i₀ : MAP Γ₀ S) (i₁ : MAP Γ₁ S) (cover : IsEquiv (copair i₀ i₁))
  (projection : MAP A S) (r : MAP X S)
  (s : Cone projection i₀ C) (t : Cone projection i₁ D)
  (es : IsPullback s) (et : IsPullback t) where
  p = Cone.right s
  q = Cone.right t
  X₀ = Pullback r i₀
  X₁ = Pullback r i₁
  r₀ : MAP X₀ Γ₀
  r₀ = pullback₂
  r₁ : MAP X₁ Γ₁
  r₁ = pullback₂
  private
    module Domain = Sum (i₀ ∘ r₀) (i₁ ∘ r₁) using (projection; module Copair)
  first : FunctorOver (i₀ ∘ r₀) r
  first = record { lift = pullback₁ ; comparison = pullbackMatch }
  second : FunctorOver (i₁ ∘ r₁) r
  second = record { lift = pullback₁ ; comparison = pullbackMatch }
  private
    module Reassembled = Domain.Copair first second using (over)
  abstract
    reassembled-isEquiv : IsEquiv (FunctorLift.lift Reassembled.over)
    reassembled-isEquiv = Cover.copair-isEquiv i₀ i₁ r
      (coneSwap (pullbackCone r i₀)) (coneSwap (pullbackCone r i₁))
      (pullback-swap (pullbackCone r i₀) (pullbackCone-isPullback r i₀))
      (pullback-swap (pullbackCone r i₁) (pullbackCone-isPullback r i₁)) cover
  private
    module Restrict = Precompose projection Reassembled.over using (functor; module Equivalence)
  private
    module Pair = Split (i₀ ∘ r₀) (i₁ ∘ r₁) projection using (functor; functor-isEquiv)

  first-target : FunctorOver p (pullback₂ {f = projection} {i₀})
  first-target = lift-triangle s
  second-target : FunctorOver q (pullback₂ {f = projection} {i₁})
  second-target = lift-triangle t
  abstract
    first-target-isEquiv : IsEquiv (FunctorLift.lift first-target)
    first-target-isEquiv = es
    second-target-isEquiv : IsEquiv (FunctorLift.lift second-target)
    second-target-isEquiv = et

  private
    module FirstPost = Postcompose r₀ first-target using (functor)
  private
    module SecondPost = Postcompose r₁ second-target using (functor)
  private
    module FirstTarget = PullbackTarget i₀ projection r₀ using (functor; functor-isEquiv)
  private
    module SecondTarget = PullbackTarget i₁ projection r₁ using (functor; functor-isEquiv)
  first-component = FirstTarget.functor ∘ FirstPost.functor
  second-component = SecondTarget.functor ∘ SecondPost.functor
  abstract
    first-component-isEquiv : IsEquiv first-component
    first-component-isEquiv = equiv-compose FirstPost.functor FirstTarget.functor
      (Post.functor-isEquiv r₀ first-target first-target-isEquiv) FirstTarget.functor-isEquiv
    second-component-isEquiv : IsEquiv second-component
    second-component-isEquiv = equiv-compose SecondPost.functor SecondTarget.functor
      (Post.functor-isEquiv r₁ second-target second-target-isEquiv) SecondTarget.functor-isEquiv
  components = productMap (IsEquiv.inverse first-component-isEquiv) (IsEquiv.inverse second-component-isEquiv)
  functor : MAP (FunOver r projection) (FunOver r₀ p × FunOver r₁ q)
  functor = components ∘ (Pair.functor ∘ Restrict.functor)
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (Pair.functor ∘ Restrict.functor) components
      (equiv-compose Restrict.functor Pair.functor
        (Restrict.Equivalence.functor-isEquiv reassembled-isEquiv) Pair.functor-isEquiv)
      (productMap-isEquiv _ _ (equiv-inverse first-component-isEquiv) (equiv-inverse second-component-isEquiv))
  private
    module Cores = ProductComparison One (FunOver r₀ p) (FunOver r₁ q) using (forward; forward-isEquiv)
  maps : MAP (MapOver r projection) (MapOver r₀ p × MapOver r₁ q)
  maps = Cores.forward ∘ mapPost functor
  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = equiv-compose (mapPost functor) Cores.forward
      (mapPost-isEquiv functor functor-isEquiv) Cores.forward-isEquiv

module Descent {C D Γ₀ Γ₁ X : CAT} (p : MAP C Γ₀) (q : MAP D Γ₁) (r : MAP X (Γ₀ ⊔ Γ₁)) where
  open Separated in₁ in₂
    (equiv-transport ((copair-inclusions Γ₀ Γ₁) ⁻¹) (id-isEquiv (Γ₀ ⊔ Γ₁)))
    (coproductMap p q) r (coneSwap (coproductSquare₁ p q)) (coneSwap (coproductSquare₂ p q))
    (pullback-swap (coproductSquare₁ p q) (inclusion₁-isPullback p q))
    (pullback-swap (coproductSquare₂ p q) (inclusion₂-isPullback p q)) public
```
