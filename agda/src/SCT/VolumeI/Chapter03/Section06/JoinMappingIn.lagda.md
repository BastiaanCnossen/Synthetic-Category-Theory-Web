# Mapping into a join by its two endpoint fibers

For a category over `Γ × [1]`, restriction to the two endpoint fibers
gives the mapping-in equivalence stated after `def:Relative_Join`.
First uncurry the join dependent product, then split the boundary by
coproduct descent. Pullback pasting identifies the two iterated fibers
with the original endpoint fibers, as functors over `Γ`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroℕ)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.JoinMappingIn
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B using (copair-β₁; copair-β₂)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.CoproductCalculus.CoproductDescent 𝒯 M ℱ P B U using (module Separated)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I using (∂[1]; boundary)
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I using (weakened-boundary; module Boundary)
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundaryCoordinates 𝒯 M B P U I using (module Cover; module Fibers)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (module MappingIn)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J using (height)

module Endpoints {C D Γ E : CAT} (p : MAP C Γ) (q : MAP D Γ) (t : MAP E (Γ × [1])) where
  module Covered = Cover Γ using (section; zero; one; equivalence; isEquiv)
  module Target = Fibers p q using (projection; module First; module Second)
  j = weakened-boundary Γ
  r : MAP (Pullback t j) (Γ × ∂[1])
  r = pullback₂
  module Split = Separated Covered.zero Covered.one Covered.isEquiv Target.projection r
    Target.First.square Target.Second.square Target.First.isPullback Target.Second.isPullback
    using (maps; maps-isEquiv; r₀; r₁)

  module Endpoint (i : MAP One ∂[1]) (e : Obj-abs [1]) (β : (boundary ∘ i) =₁ e) where
    section = Covered.section i
    interval-section : MAP Γ (Γ × [1])
    interval-section = pair (id Γ) (const e)
    fiber = Pullback t interval-section
    projection : MAP fiber Γ
    projection = pullback₂
    iterated-projection : MAP (Pullback r section) Γ
    iterated-projection = pullback₂
    comparison : (j ∘ section) =₁ interval-section
    comparison = Boundary.component p q (id Γ) i e β
    right = coneSwap (pullbackCone t j)
    inner = coneSwap (pullbackCone r section)
    pasted = PasteCones.flatten section j right inner
    changed = changeLeft comparison pasted
    square : Cone t interval-section (Pullback r section)
    square = coneSwap changed
    abstract
      right-isPullback : IsPullback right
      right-isPullback = pullback-swap (pullbackCone t j) (pullbackCone-isPullback t j)
      inner-isPullback : IsPullback inner
      inner-isPullback = pullback-swap (pullbackCone r section) (pullbackCone-isPullback r section)
      square-isPullback : IsPullback square
      square-isPullback = pullback-swap changed
        (ChangeLeft.preserve comparison t pasted
          (Pasting.paste-isPullback section j t right right-isPullback inner inner-isPullback))
    inclusion : FunctorOver iterated-projection projection
    inclusion = lift-triangle square
    module Restrict {A : CAT} (f : MAP A Γ) where
      module Chosen = Precompose f inclusion using (maps; module Equivalence)
      maps : MAP (MapOver projection f) (MapOver iterated-projection f)
      maps = Chosen.maps
      abstract
        maps-isEquiv : IsEquiv maps
        maps-isEquiv = Chosen.Equivalence.maps-isEquiv square-isPullback

  module Zero = Endpoint in₁ zero (copair-β₁ zero one) using (fiber; projection; module Restrict)
  module One = Endpoint in₂ one (copair-β₂ zero one) using (fiber; projection; module Restrict)
  E₀ = Zero.fiber
  E₁ = One.fiber
  module Left = Zero.Restrict p using (maps; maps-isEquiv)
  module Right = One.Restrict q using (maps; maps-isEquiv)
  components = productMap (IsEquiv.inverse Left.maps-isEquiv) (IsEquiv.inverse Right.maps-isEquiv)
  boundary-maps : MAP (MapOver r Target.projection) (MapOver Zero.projection p × MapOver One.projection q)
  boundary-maps = components ∘ Split.maps
  abstract
    boundary-maps-isEquiv : IsEquiv boundary-maps
    boundary-maps-isEquiv = equiv-compose Split.maps components Split.maps-isEquiv
      (productMap-isEquiv _ _ (equiv-inverse Left.maps-isEquiv) (equiv-inverse Right.maps-isEquiv))
  module Uncurry = MappingIn p q t using (uncurry; uncurry-isEquiv)
  maps : MAP (MapOver t (height p q)) (MapOver Zero.projection p × MapOver One.projection q)
  maps = boundary-maps ∘ Uncurry.uncurry
  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = equiv-compose Uncurry.uncurry boundary-maps Uncurry.uncurry-isEquiv boundary-maps-isEquiv
```
