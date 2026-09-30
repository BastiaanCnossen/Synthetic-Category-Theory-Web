# Product frames for the precomposition triangles

The normalized product associativity law identifies the two product
routes to the common middle of a precomposition triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionProductFrameComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionTriangleFrames as Frames
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionAssociativity as Associativity

module At {C D : CAT} (K : CAT) (l : MAP C D) (r : MAP D C)
  (u : funUncurry (funPre {D = K} l ∘ funPre {D = K} r) =₁
    (funEval ∘ pair (pr₁ {Fun C K} {C}) (r ∘ (l ∘ pr₂)))) where
  module F = Frames.At 𝒯 M ℱ K l r u
  module Triple = Associativity.At 𝒯 M (Fun C K) r l r
  Jl : MAP (F.X × C) (F.X × D)
  Jl = productMap (id F.X) l
  Jlr : MAP (F.X × D) (F.X × D)
  Jlr = productMap (id F.X) (l ∘ r)
  δrl = pair-cong (comp-unitˡ (pr₁ {F.X} {C})) (comp-assoc (pr₂ {F.X} {C}) l r)
  δlr = pair-cong (comp-unitˡ (pr₁ {F.X} {D})) (comp-assoc (pr₂ {F.X} {D}) r l)
  ψ = Triple.Right.ψ

  abstract
    value : (F.product-frame ∙ ((δrl ∙ productRestriction-comp F.X l r) ▷ F.W)) =₂
      (ψ ∙ ((F.W ◁ productRestriction-comp F.X r l) ∙ comp-assoc F.W Jl F.W))
    value = Triple.value
```
