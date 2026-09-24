# Restricting a corner with specified vertex frames

A comparison between two shape boundaries carries their whole endpoint
cone. We express its source matching as a quotient of vertex frames,
while retaining the actual restriction comparisons on the two edges.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.RestrictionBoundaryCorners as Boundary
import SCT.VolumeI.Chapter02.Section02.EndpointFrameCones as Frames

module SCT.VolumeI.Chapter02.Section02.FramedRestrictionCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.RestrictionEvaluation 𝒯 M ℱ P public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 public
open Frames 𝒯 M ℱ P using (frame; framed-cone; replace-matchings) public

module At {Γ A D K B C : CAT} (u : Obj-abs A) (v : Obj-abs D)
  (d : MAP A K) (k : MAP D K) (j : MAP K B)
  (δ : (d ∘ u) =₁ (k ∘ v))
  (r : MAP A B) (s : MAP D B)
  (α : (j ∘ d) =₁ r) (β : (j ∘ k) =₁ s)
  {z : Obj-abs B} (b : (r ∘ u) =₁ z) (e : (s ∘ v) =₁ z)
  (shape : ((e ⁻¹ ∙ b) ∙ Boundary.Edge.vertex 𝒯 M ℱ P {C = C} d j r α u) =₂
    (Boundary.Edge.vertex 𝒯 M ℱ P {C = C} k j s β v ∙ (j ◁ δ)))
  (W : MAP Γ (Fun B C)) where
  module Corner = Boundary.Corner 𝒯 M ℱ P {C = C} u v d k j δ r s α β (e ⁻¹ ∙ b) shape
  module Family = Corner.Family W
  module Framing = Frames.At 𝒯 M ℱ P r s u v b e W

  comparison : ConeIso
    (framed-cone (funPre r ∘ W) (funPre s ∘ W) (frame r u b W) (frame s v e W))
    (conePre (funPre j ∘ W) Corner.Inner.cone)
  comparison = replace-matchings Family.value _ _ Framing.matching (idIso _)
```
