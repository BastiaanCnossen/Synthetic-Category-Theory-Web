# Triangle presentations with a prescribed endpoint matching

The constant-side triangle square can use a matching whose endpoint image
is the actual curried evaluation route. Normalize its matching along
evaluation. The correction gives a cone isomorphism, which retains its
pullback property. The endpoint equation is retained for later pasting.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowSquares as ArrowSquares
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEvaluationCorners as Corners
import SCT.VolumeI.Chapter02.Section02.TrianglePullbacks as TriangleSquares
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.SplitRetractionMatching as Matching

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.NormalizedSliceTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareRetractions 𝒯 M ℱ P I E Q
  using (p₂; p₂-j₁; p₀; p₀-j₀; j₀; j₁)

module Slice {C : CAT} (x : Obj-abs C) where
  module Endpoint = ArrowSquares.Endpoint 𝒯 M ℱ P I C one x
    using (nested; swapped; side; side-comparison)
  module Corner = Corners.At 𝒯 M ℱ P I E S Endpoint.swapped using (comparison)
  module Known = TriangleSquares.At.Right 𝒯 M ℱ P I E S Q C
    using (vertex-square; vertex-square-isPullback)

  k : MAP (Triangles C) (Fun ([1] × [1]) C)
  k = funPre p₂
  nested : MAP (Triangles C) (Ar (Ar C))
  nested = Endpoint.nested ∘ k

  swap-triangle : (swap ∘ j₀) =₁ j₁
  swap-triangle = pair-cong (pair-β₂ s₀ s₁) (pair-β₁ s₀ s₁) ∙ pair-pre pr₂ pr₁ j₀

  restriction : ((funPre j₀ ∘ Endpoint.swapped) ∘ k) =₁ id (Triangles C)
  restriction = funPre-id [2] C ∙ (funPre-cong p₂-j₁ ∙
    (funPre-comp j₁ p₂ ∙ ((funPre-cong swap-triangle ∙ funPre-comp j₀ swap) ▷ k)))

  edge : (ev₁ ∘ nested) =₁ edge₀
  edge = comp-unitʳ edge₀ ∙ ((edge₀ ◁ restriction) ∙
    (comp-assoc k (funPre j₀ ∘ Endpoint.swapped) edge₀ ∙
    ((ConeIso.rightIso Corner.comparison ▷ k) ∙ (comp-assoc k Endpoint.nested ev₁) ⁻¹)))

  side : (funPost ev₁ ∘ nested) =₁ (Endpoint.side ∘ k)
  side = (Endpoint.side-comparison ▷ k) ∙ (comp-assoc k Endpoint.nested (funPost ev₁)) ⁻¹

  vertex : (ev₁ ∘ edge₀ {C}) =₁ evaluate vertex₂
  vertex = evaluate-cong d₀-one ∙ evaluate-pre d₀ one

  evaluation-endpoint : (ev₁ ∘ (funPost ev₁ ∘ nested)) =₁ evaluate vertex₂
  evaluation-endpoint = vertex ∙ ((ev₁ ◁ edge) ∙ evaluate-post-at one ev₁ nested)

  endpoint : (ev₁ ∘ (Endpoint.side ∘ k)) =₁ evaluate vertex₂
  endpoint = evaluation-endpoint ∙ (ev₁ ◁ side) ⁻¹

  module Normalized = Matching.WithRetraction.Normalize 𝒯 identityArrow ev₁ identity-target
    (Cone.match Known.vertex-square) endpoint using (matching; image-law; correction)
  module EndpointRetraction = Matching.WithRetraction 𝒯 (identityArrow {C}) ev₁ identity-target
    using (frame; precompose-image)

  full-matching : (funPost ev₁ ∘ nested) =₁ (identityArrow ∘ evaluate vertex₂)
  full-matching = Normalized.matching ∙ side

  abstract
    full-image : (EndpointRetraction.frame (evaluate vertex₂) ∙ (ev₁ ◁ full-matching)) =₂ evaluation-endpoint
    full-image = EndpointRetraction.precompose-image Normalized.matching side evaluation-endpoint Normalized.image-law

  square : Cone Endpoint.side (identityArrow {C}) (Triangles C)
  square = record { left = k ; right = evaluate vertex₂ ; match = Normalized.matching }

  comparison : ConeIso Known.vertex-square square
  comparison = record
    { leftIso = idIso k ; rightIso = Normalized.correction
    ; compatible = isoComp-unitʳ-at Normalized.matching ∙
        isoComp-cong (idIso Normalized.matching) (postWhisker-idIso Endpoint.side k) }

  abstract
    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant comparison Known.vertex-square-isPullback

module Coslice {C : CAT} (x : Obj-abs C) where
  module Endpoint = ArrowSquares.Endpoint 𝒯 M ℱ P I C zero x
    using (nested; swapped; side; side-comparison)
  module Corner = Corners.Dual 𝒯 M ℱ P I E S Endpoint.swapped using (comparison)
  module Known = TriangleSquares.At.Left 𝒯 M ℱ P I E S Q C
    using (vertex-square; vertex-square-isPullback)

  k : MAP (Triangles C) (Fun ([1] × [1]) C)
  k = funPre p₀
  nested : MAP (Triangles C) (Ar (Ar C))
  nested = Endpoint.nested ∘ k

  swap-triangle : (swap ∘ j₁) =₁ j₀
  swap-triangle = pair-cong (pair-β₂ s₁ s₀) (pair-β₁ s₁ s₀) ∙ pair-pre pr₂ pr₁ j₁

  restriction : ((funPre j₁ ∘ Endpoint.swapped) ∘ k) =₁ id (Triangles C)
  restriction = funPre-id [2] C ∙ (funPre-cong p₀-j₀ ∙
    (funPre-comp j₀ p₀ ∙ ((funPre-cong swap-triangle ∙ funPre-comp j₁ swap) ▷ k)))

  edge : (ev₀ ∘ nested) =₁ edge₂
  edge = comp-unitʳ edge₂ ∙ ((edge₂ ◁ restriction) ∙
    (comp-assoc k (funPre j₁ ∘ Endpoint.swapped) edge₂ ∙
    ((ConeIso.rightIso Corner.comparison ▷ k) ∙ (comp-assoc k Endpoint.nested ev₀) ⁻¹)))

  side : (funPost ev₀ ∘ nested) =₁ (Endpoint.side ∘ k)
  side = (Endpoint.side-comparison ▷ k) ∙ (comp-assoc k Endpoint.nested (funPost ev₀)) ⁻¹

  vertex : (ev₀ ∘ edge₂ {C}) =₁ evaluate vertex₀
  vertex = evaluate-cong d₂-zero ∙ evaluate-pre d₂ zero

  evaluation-endpoint : (ev₀ ∘ (funPost ev₀ ∘ nested)) =₁ evaluate vertex₀
  evaluation-endpoint = vertex ∙ ((ev₀ ◁ edge) ∙ evaluate-post-at zero ev₀ nested)

  endpoint : (ev₀ ∘ (Endpoint.side ∘ k)) =₁ evaluate vertex₀
  endpoint = evaluation-endpoint ∙ (ev₀ ◁ side) ⁻¹

  module Normalized = Matching.WithRetraction.Normalize 𝒯 identityArrow ev₀ identity-source
    (Cone.match Known.vertex-square) endpoint using (matching; image-law; correction)
  module EndpointRetraction = Matching.WithRetraction 𝒯 (identityArrow {C}) ev₀ identity-source
    using (frame; precompose-image)

  full-matching : (funPost ev₀ ∘ nested) =₁ (identityArrow ∘ evaluate vertex₀)
  full-matching = Normalized.matching ∙ side

  abstract
    full-image : (EndpointRetraction.frame (evaluate vertex₀) ∙ (ev₀ ◁ full-matching)) =₂ evaluation-endpoint
    full-image = EndpointRetraction.precompose-image Normalized.matching side evaluation-endpoint Normalized.image-law

  square : Cone Endpoint.side (identityArrow {C}) (Triangles C)
  square = record { left = k ; right = evaluate vertex₀ ; match = Normalized.matching }

  comparison : ConeIso Known.vertex-square square
  comparison = record
    { leftIso = idIso k ; rightIso = Normalized.correction
    ; compatible = isoComp-unitʳ-at Normalized.matching ∙
        isoComp-cong (idIso Normalized.matching) (postWhisker-idIso Endpoint.side k) }

  abstract
    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant comparison Known.vertex-square-isPullback
```
