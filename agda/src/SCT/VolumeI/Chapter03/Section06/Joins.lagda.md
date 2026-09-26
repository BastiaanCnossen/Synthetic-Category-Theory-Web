# Joins, cones, and their universal properties

The absolute join is the relative join over `One`. The pushout axiom
gives its mapping-out property, including the specified matching, and
the second axiom gives its mapping-in property over the height base.
These are `rmk:Mapping_Out_Of_Join` and `def:Relative_Join`.

The last definitions record `def:Left_And_Right_Cones` and the recursive
simplex notation. The natural-number index here belongs to Agda's
metalanguage, not to an additional internal natural-number axiom.

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

module SCT.VolumeI.Chapter03.Section06.Joins
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ hiding (_⋆_)
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (functorOut)
open import SCT.VolumeI.Chapter01.Section08.MappingOutOfPushouts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J

infixr 5 _⋆_
_⋆_ : CAT → CAT → CAT
C ⋆ D = JoinOver (terminate C) (terminate D)

join-in₁ : {C D : CAT} → MAP C (C ⋆ D)
join-in₁ {C} {D} = inclusion (terminate C) (terminate D) ∘ in₁

join-in₂ : {C D : CAT} → MAP D (C ⋆ D)
join-in₂ {C} {D} = inclusion (terminate C) (terminate D) ∘ in₂

module MappingOut {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) (Γ-isAn : isAn Γ) where
  module Pushout = JoinPushout (mapping-out p q Γ-isAn)

  functor-square-isPullback : (E : CAT) → IsPullback (functorOut Pushout.square E)
  functor-square-isPullback = pushout→functor-criterion Pushout.square Pushout.universal

join-dependent-product : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) →
  DependentProduct (weakened-boundary Γ) (Boundary.projection p q)
join-dependent-product p q = record
  { category = JoinOver p q ; projection = height p q
  ; evaluation = BoundaryComparison.evaluation dataJoin p q (boundary-isEquiv p q)
  ; isDependentProduct = mapping-in p q }

module MappingIn {C D Γ E : CAT} (p : MAP C Γ) (q : MAP D Γ) (t : MAP E (Γ × [1])) =
  RelativeCurrying.At (weakened-boundary Γ) (Boundary.projection p q) (join-dependent-product p q) t

leftCone : CAT → CAT
leftCone C = One ⋆ C

rightCone : CAT → CAT
rightCone C = C ⋆ One

simplex : Nat → CAT
simplex zeroℕ = One
simplex (suc n) = rightCone (simplex n)
```
