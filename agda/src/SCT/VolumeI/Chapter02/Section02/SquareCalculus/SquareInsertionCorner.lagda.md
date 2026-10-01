# The three projections of the insertion corner

Inserting the two coordinates in opposite orders gives the existing
`insert-natural` square. Its parameter, inner, and outer projection
equations follow from the retained insertion witnesses. The two interval
coordinates are never silently exchanged.

These equations supply the input to the remaining comparison between
the two boundary routes in `SquareCurryingCoordinates`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareInsertionCorner
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates as Rectangles
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionProjectionWitnesses as Insertion
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
module PS = Projections 𝒯
  using (Square; lift-base; lift-square)

module At (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module Coordinates = Rectangles.Coordinates 𝒯 M ℱ Γ A B
  module H = Coordinates.Horizontal u
  module V = Coordinates.Vertical v
  module Insert = Insertion.Parameter 𝒯 M ℱ (insert {X = Γ} v) u
  ia = insert {X = Γ} u
  ib = insert {X = Γ} v

  corner : (H.step ∘ ib) =₁ (V.step ∘ ia)
  corner = insert-natural ib u

  parameter-incoming : (Coordinates.parameter ∘ (H.step ∘ ib)) =₁ (id Γ)
  parameter-incoming = pair-β₁ (id Γ) (const v) ∙ PS.lift-base pr₁ pr₁ _ Insert.incoming₁
  parameter-outgoing : (Coordinates.parameter ∘ (V.step ∘ ia)) =₁ (id Γ)
  parameter-outgoing = pair-β₁ (id Γ) (const v) ∙ PS.lift-base pr₁ pr₁ _ Insert.outgoing₁

  outer-incoming : (Coordinates.outer ∘ (H.step ∘ ib)) =₁ (const v)
  outer-incoming = pair-β₂ (id Γ) (const v) ∙ PS.lift-base pr₂ pr₁ _ Insert.incoming₁
  outer-outgoing : (Coordinates.outer ∘ (V.step ∘ ia)) =₁ (const v)
  outer-outgoing = pair-β₂ (id Γ) (const v) ∙ PS.lift-base pr₂ pr₁ _ Insert.outgoing₁

  abstract
    parameter-square : PS.Square Coordinates.parameter parameter-incoming parameter-outgoing corner
    parameter-square = isoComp-cong (idIso (pair-β₁ (id Γ) (const v)))
        (PS.lift-square pr₁ pr₁ Insert.incoming₁ Insert.outgoing₁ corner Insert.projection₁) ∙
      isoComp-assoc-at (pair-β₁ (id Γ) (const v))
        (PS.lift-base pr₁ pr₁ _ Insert.outgoing₁) (Coordinates.parameter ◁ corner)

    inner-square : PS.Square Coordinates.inner Insert.incoming₂ Insert.outgoing₂ corner
    inner-square = Insert.projection₂

    outer-square : PS.Square Coordinates.outer outer-incoming outer-outgoing corner
    outer-square = isoComp-cong (idIso (pair-β₂ (id Γ) (const v)))
        (PS.lift-square pr₂ pr₁ Insert.incoming₁ Insert.outgoing₁ corner Insert.projection₁) ∙
      isoComp-assoc-at (pair-β₂ (id Γ) (const v))
        (PS.lift-base pr₂ pr₁ _ Insert.outgoing₁) (Coordinates.outer ◁ corner)
```
