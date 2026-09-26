# Postcomposing the common base of native functors

A functor between bases carries native triangles and their comparisons
to the new base. The composition comparison is the projection-square
pasting calculation from Chapter 1. This operation does not assert any
contextual extension of the category constructors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as ProjectionSquares

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (triangle-identification)
module PS = ProjectionSquares 𝒯

postbase : {C D S T : CAT} (p : MAP S T) {f : MAP C S} {g : MAP D S} →
  FunctorOver f g → FunctorOver (p ∘ f) (p ∘ g)
postbase p {g = g} u = record { lift = FunctorLift.lift u
  ; comparison = PS.lift-base p g (FunctorLift.lift u) (FunctorLift.comparison u) }

postbase-iso : {C D S T : CAT} (p : MAP S T) {f : MAP C S} {g : MAP D S}
  {u v : FunctorOver f g} → FunctorOverIso u v → FunctorOverIso (postbase p u) (postbase p v)
postbase-iso p {g = g} {u} {v} Φ = record { underlying = FunctorOverIso.underlying Φ
  ; compatible = PS.lift-square p g (FunctorLift.comparison u) (FunctorLift.comparison v)
      (FunctorOverIso.underlying Φ) (FunctorOverIso.compatible Φ) }

abstract
  postbase-composite : {B C D S T : CAT} (p : MAP S T)
    {f : MAP B S} {g : MAP C S} {h : MAP D S}
    (u : FunctorOver f g) (v : FunctorOver g h) →
    FunctorOverIso (compose-over (postbase p v) (postbase p u)) (postbase p (compose-over v u))
  postbase-composite p {h = h} u v = triangle-identification _ _ _
    (PS.lift-compose p h (FunctorLift.lift v) (FunctorLift.lift u)
      (FunctorLift.comparison v) (FunctorLift.comparison u))
```
