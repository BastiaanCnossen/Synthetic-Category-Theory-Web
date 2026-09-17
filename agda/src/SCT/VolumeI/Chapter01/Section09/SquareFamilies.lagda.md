# Gluing families of triangles

The functor-category formulation of the square axiom follows from §1.8.
Its pullback property gives gluing in any common categorical context.
The comparison below retains the identification along the common edge.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter01.Section09.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter01.Section09.SquareFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section09.SquareShape 𝒯 M ℱ P I E
open Squares.CommutativeSquareAxiom Q
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.FunctorCriterionPreservation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P

square-functor-pullback : (C : CAT) → IsPullback (functorOut gluing-square C)
square-functor-pullback = pushout→functor-criterion gluing-square square-isPushout

module Families (C : CAT) where
  module U = UniversalCone (functorOut gluing-square C) (square-functor-pullback C)

  square-in : {Γ : CAT} → Cone (funPre {D = C} d₁) (funPre d₁) Γ →
    MAP Γ (Fun ([1] × [1]) C)
  square-in = U.factor

  square-in-β : {Γ : CAT} (t : Cone (funPre {D = C} d₁) (funPre d₁) Γ) →
    ConeIso (conePre (square-in t) (functorOut gluing-square C)) t
  square-in-β = U.factor-β

  square-in-η : {Γ : CAT} (h : MAP Γ (Fun ([1] × [1]) C)) →
    =₁ (square-in (conePre h (functorOut gluing-square C))) h
  square-in-η = U.factor-η
```
