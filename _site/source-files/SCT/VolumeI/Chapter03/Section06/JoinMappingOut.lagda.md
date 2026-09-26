# Mapping out of a join

This is the product form of `rmk:Mapping_Out_Of_Join`. A functor on
the cylinder is attached to a functor on each endpoint category.
Distributivity and restriction from coproducts identify the boundary
functor categories with products. The resulting square uses the actual
restrictions along the two join inclusions.

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

module SCT.VolumeI.Chapter03.Section06.JoinMappingOut
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ hiding (_⋆_)
open Coproducts.CoproductStructure B
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (pair-after)
open import SCT.VolumeI.Chapter01.Section07.CoproductDomain 𝒯 M B P U ℱ using (module CoproductDomain)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.EquivalentCospanCone 𝒯 P using (module Transport)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneRetarget; coneRetarget-β)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (functorOut)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpanCoordinates 𝒯 M ℱ B P U I J using (insert)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.NormalizedJoinPushout 𝒯 M ℱ B P U I J using (module Normalized)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_; join-in₁; join-in₂)

module MappingOut (C D E : CAT) where
  module Join = Normalized C D
  module Boundary = CoproductDomain C D E
  module Endpoints = CoproductDomain (C × D) (C × D) E
  cylinder-endpoints : MAP (Fun ((C × D) × [1]) E) (Fun (C × D) E × Fun (C × D) E)
  cylinder-endpoints = pair (funPre (insert zero)) (funPre (insert one))
  boundary-projections : MAP (Fun C E × Fun D E) (Fun (C × D) E × Fun (C × D) E)
  boundary-projections = productMap (funPre pr₁) (funPre pr₂)
  abstract
    top-normal : (Endpoints.forward ∘ funPre Join.top) =₁ cylinder-endpoints
    top-normal = pair-cong
      (funPre-cong (copair-β₁ (insert zero) (insert one)) ∙ funPre-comp in₁ Join.top)
      (funPre-cong (copair-β₂ (insert zero) (insert one)) ∙ funPre-comp in₂ Join.top) ∙
      pair-pre (funPre in₁) (funPre in₂) (funPre Join.top)
    bottom-normal : (Endpoints.forward ∘ funPre Join.bottom) =₁
      pair (funPre (in₁ ∘ pr₁)) (funPre (in₂ ∘ pr₂))
    bottom-normal = pair-cong
      (funPre-cong (copair-β₁ (in₁ ∘ pr₁) (in₂ ∘ pr₂)) ∙ funPre-comp in₁ Join.bottom)
      (funPre-cong (copair-β₂ (in₁ ∘ pr₁) (in₂ ∘ pr₂)) ∙ funPre-comp in₂ Join.bottom) ∙
      pair-pre (funPre in₁) (funPre in₂) (funPre Join.bottom)
    projections-normal : (boundary-projections ∘ Boundary.forward) =₁
      pair (funPre (in₁ ∘ pr₁)) (funPre (in₂ ∘ pr₂))
    projections-normal = pair-cong (funPre-comp pr₁ in₁) (funPre-comp pr₂ in₂) ∙
      pair-after (funPre pr₁) (funPre pr₂) (funPre in₁) (funPre in₂)
  cospan : CospanMap (funPre Join.top) (funPre Join.bottom) cylinder-endpoints boundary-projections
  cospan = record { left = id (Fun ((C × D) × [1]) E) ; right = Boundary.forward ; base = Endpoints.forward
    ; leftSquare = top-normal ⁻¹ ∙ comp-unitʳ cylinder-endpoints
    ; rightSquare = bottom-normal ⁻¹ ∙ projections-normal }
  module Changed = Transport cospan (id-isEquiv (Fun ((C × D) × [1]) E))
    Boundary.forward-isEquiv Endpoints.forward-isEquiv (functorOut Join.square E) (Join.functor-square-isPullback E)
    using (cone; isPullback)
  restriction : MAP (Fun (C ⋆ D) E) (Fun C E × Fun D E)
  restriction = pair (funPre join-in₁) (funPre join-in₂)
  abstract
    boundary-comparison : (Boundary.forward ∘ funPre Join.boundary) =₁ restriction
    boundary-comparison = pair-cong (funPre-comp in₁ Join.boundary) (funPre-comp in₂ Join.boundary) ∙
      pair-pre (funPre in₁) (funPre in₂) (funPre Join.boundary)
  cone : Cone cylinder-endpoints boundary-projections (Fun (C ⋆ D) E)
  cone = coneRetarget Changed.cone (funPre Join.cylinder) restriction
    (comp-unitˡ (funPre Join.cylinder)) boundary-comparison
  abstract
    isPullback : IsPullback cone
    isPullback = pullback-cone-invariant
      (coneRetarget-β Changed.cone (funPre Join.cylinder) restriction
        (comp-unitˡ (funPre Join.cylinder)) boundary-comparison) Changed.isPullback
```
