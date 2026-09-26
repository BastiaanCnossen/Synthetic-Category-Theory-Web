# The triangle faces at the corners of a square

The three chosen face identifications retain their images under both
degeneracies. Pairing those equations gives the vertex equations for
both triangles of the square, including their common diagonal.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.MiddleVertex as Middle
import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.OuterVertices as Outer
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.PairedFaceCorners as Pairing
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareFaceCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareShape 𝒯 M ℱ P I E public
module PS = Projection 𝒯
module Mid = Middle 𝒯 M ℱ P I E
module Out = Outer 𝒯 M ℱ P I E
module Pair = Pairing 𝒯 M ℱ

module UpperMiddle where
  module Face = Pair.At s₀ s₁ d₂ d₀ one zero
    s₀-d₂ s₁-d₂ s₀-d₀ s₁-d₀
    (constant-boundary one zero) (comp-unitˡ one)
    (comp-unitˡ zero) (constant-boundary zero one) (face-middle ⁻¹)
  first = PS.inverse-square s₀ Mid.source-before Mid.source-after face-middle Mid.source-compatible
  second = PS.inverse-square s₁ Mid.target-before Mid.target-after face-middle Mid.target-compatible
  corner = Face.corner first second

module LowerMiddle where
  module Face = Pair.At s₁ s₀ d₀ d₂ zero one
    s₁-d₀ s₀-d₀ s₁-d₂ s₀-d₂
    (constant-boundary zero one) (comp-unitˡ zero)
    (comp-unitˡ one) (constant-boundary one zero) face-middle
  corner = Face.corner Mid.target-compatible Mid.source-compatible

module UpperSource where
  module Face = Pair.At s₀ s₁ d₁ d₂ zero zero
    s₀-d₁ s₁-d₁ s₀-d₂ s₁-d₂
    (comp-unitˡ zero) (comp-unitˡ zero)
    (constant-boundary zero zero) (comp-unitˡ zero) face-bottom
  corner = Face.corner Out.Bottom.source-compatible Out.Bottom.target-compatible

module LowerSource where
  module Face = Pair.At s₁ s₀ d₁ d₂ zero zero
    s₁-d₁ s₀-d₁ s₁-d₂ s₀-d₂
    (comp-unitˡ zero) (comp-unitˡ zero)
    (comp-unitˡ zero) (constant-boundary zero zero) face-bottom
  corner = Face.corner Out.Bottom.target-compatible Out.Bottom.source-compatible

module UpperTarget where
  module Face = Pair.At s₀ s₁ d₀ d₁ one one
    s₀-d₀ s₁-d₀ s₀-d₁ s₁-d₁
    (comp-unitˡ one) (constant-boundary one one)
    (comp-unitˡ one) (comp-unitˡ one) face-top
  corner = Face.corner Out.Top.source-compatible Out.Top.target-compatible

module LowerTarget where
  module Face = Pair.At s₁ s₀ d₀ d₁ one one
    s₁-d₀ s₀-d₀ s₁-d₁ s₀-d₁
    (constant-boundary one one) (comp-unitˡ one)
    (comp-unitˡ one) (comp-unitˡ one) face-top
  corner = Face.corner Out.Top.target-compatible Out.Top.source-compatible

module LowerMiddleForward where
  module Face = Pair.At s₁ s₀ d₂ d₀ one zero
    s₁-d₂ s₀-d₂ s₁-d₀ s₀-d₀
    (comp-unitˡ one) (constant-boundary one zero)
    (constant-boundary zero one) (comp-unitˡ zero) (face-middle ⁻¹)
  first = UpperMiddle.second
  second = UpperMiddle.first
  corner = Face.corner first second

module UpperTargetBack where
  module Face = Pair.At s₀ s₁ d₁ d₀ one one
    s₀-d₁ s₁-d₁ s₀-d₀ s₁-d₀
    (comp-unitˡ one) (comp-unitˡ one)
    (comp-unitˡ one) (constant-boundary one one) (face-top ⁻¹)
  first = PS.inverse-square s₀ Out.Top.source-before Out.Top.source-after face-top Out.Top.source-compatible
  second = PS.inverse-square s₁ Out.Top.target-before Out.Top.target-after face-top Out.Top.target-compatible
  corner = Face.corner first second

module LowerTargetBack where
  module Face = Pair.At s₁ s₀ d₁ d₀ one one
    s₁-d₁ s₀-d₁ s₁-d₀ s₀-d₀
    (comp-unitˡ one) (comp-unitˡ one)
    (constant-boundary one one) (comp-unitˡ one) (face-top ⁻¹)
  corner = Face.corner UpperTargetBack.second UpperTargetBack.first
```
