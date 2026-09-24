# Currying a square and identifying its four sides

Double currying uses the explicit permutation of the two diagram
coordinates. Evaluation of the outer variable yields the vertical sides;
postcomposition by evaluation of the inner variable yields the horizontal
sides. Reflected comparisons retain their uncurried images.

These are side comparisons. `SquareCornerEvaluation` separately proves
their compatibility at the four corners, retaining the specified
shape-corner identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.SquareCurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
import SCT.VolumeI.Chapter02.Section02.SquareCurryingCoordinates as Rectangles

module At {Γ A B C : CAT} (W : MAP Γ (Fun (A × B) C)) where
  module Coordinates = Rectangles.Coordinates 𝒯 M ℱ Γ A B
  H : MAP (Γ × (A × B)) C
  H = funUncurry W
  diagram : MAP ((Γ × B) × A) C
  diagram = H ∘ Coordinates.permute
  first-curry : MAP (Γ × B) (Fun A C)
  first-curry = funCurry diagram
  nested : MAP Γ (Fun B (Fun A C))
  nested = funCurry first-curry

  module Vertical (v : Obj-abs B) where
    module Coordinate = Coordinates.Vertical v
    side : MAP Γ (Fun A C)
    side = funPre (insert v) ∘ W
    raw : funUncurry (first-curry ∘ insert v) =₁ funUncurry side
    raw = (funPre-uncurry (insert v) W) ⁻¹ ∙
      ((H ◁ Coordinate.comparison) ∙
      (comp-assoc Coordinate.step Coordinates.permute H ∙
      ((funCurry-β diagram ▷ Coordinate.step) ∙ funUncurry-restrict first-curry (insert v))))

    restricted : (first-curry ∘ insert v) =₁ side
    restricted = funIsoReflect _ _ raw
    restricted-β : funUncurryIso restricted =₂ raw
    restricted-β = funIsoReflect-β _ _ raw

    boundary : (evaluate v ∘ nested) =₁ side
    boundary = restricted ∙ evaluate-curry v first-curry

  module Horizontal (u : Obj-abs A) where
    module Coordinate = Coordinates.Horizontal u
    side : MAP Γ (Fun B C)
    side = funPre (Rectangles.coinsert 𝒯 M ℱ u) ∘ W
    evaluated : MAP Γ (Fun B C)
    evaluated = funPost (evaluate u) ∘ nested
    raw : funUncurry evaluated =₁ funUncurry side
    raw = (funPre-uncurry (Rectangles.coinsert 𝒯 M ℱ u) W) ⁻¹ ∙
      ((H ◁ Coordinate.comparison) ∙
      (comp-assoc Coordinate.step Coordinates.permute H ∙
      (evaluate-curry u diagram ∙
      ((evaluate u ◁ funCurry-β first-curry) ∙ funPost-uncurry (evaluate u) nested))))

    comparison : evaluated =₁ side
    comparison = funIsoReflect _ _ raw
    comparison-β : funUncurryIso comparison =₂ raw
    comparison-β = funIsoReflect-β _ _ raw
```
