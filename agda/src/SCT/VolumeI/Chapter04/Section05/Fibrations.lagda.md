# Cartesian and cocartesian fibrations

These are the two definitions in `def:Cocartesian_Fibration`. The
directed source evaluation has a left adjoint section in the
cocartesian case; the directed target evaluation has a right adjoint
section in the cartesian case. The records retain the chosen lift and
its adjunction data. No claim of uniqueness of that data is made here.

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

module SCT.VolumeI.Chapter04.Section05.Fibrations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
  using (module Evaluation)

module Fibration {A B : CAT} (f : MAP A B) where
  open Evaluation f

  record CocartesianFibration : Set m where
    field
      lift : MAP Left.category (Ar A)
      left-adjoint-section : LeftAdjointSection directed-ev₀ lift

  record CartesianFibration : Set m where
    field
      lift : MAP Right.category (Ar A)
      right-adjoint-section : RightAdjointSection directed-ev₁ lift
```
