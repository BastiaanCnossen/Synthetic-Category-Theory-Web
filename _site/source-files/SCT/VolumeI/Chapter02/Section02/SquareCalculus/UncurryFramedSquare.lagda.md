# Recovering a square from an arrow in the arrow category

Undo the explicit permutation of the parameter and interval coordinates,
then curry once. Currying the resulting square twice recovers the original
arrow. Only the stated one-sided inverse of the permutation is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurrying as Currying
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates as Coordinates

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.UncurryFramedSquare
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public

module Permutation (Γ A B : CAT) where
  module Coordinate = Coordinates.Coordinates 𝒯 M ℱ Γ A B
  J = Coordinate.permute
  first : MAP (Γ × (A × B)) (Γ × B)
  first = pair pr₁ (pr₂ ∘ pr₂)
  last : MAP (Γ × (A × B)) A
  last = pr₁ ∘ pr₂
  backward : MAP (Γ × (A × B)) ((Γ × B) × A)
  backward = pair first last

  parameter : (pr₁ ∘ J) =₁ (pr₁ ∘ pr₁)
  parameter = pair-β₁ Coordinate.parameter Coordinate.rectangle
  outer : ((pr₂ ∘ pr₂) ∘ J) =₁ (pr₂ ∘ pr₁)
  outer = pair-β₂ Coordinate.inner Coordinate.outer ∙
    (pr₂ ◁ pair-β₂ Coordinate.parameter Coordinate.rectangle) ∙ comp-assoc J pr₂ pr₂
  inner : (last ∘ J) =₁ pr₂
  inner = pair-β₁ Coordinate.inner Coordinate.outer ∙
    (pr₁ ◁ pair-β₂ Coordinate.parameter Coordinate.rectangle) ∙ comp-assoc J pr₂ pr₁

  backward-forward : (backward ∘ J) =₁ (id ((Γ × B) × A))
  backward-forward = pair-projections ∙
    pair-cong (pair-η pr₁) (idIso pr₂) ∙
    pair-cong (pair-cong parameter outer ∙ pair-pre pr₁ (pr₂ ∘ pr₂) J) inner ∙
    pair-pre first last J

module At {Γ A B C : CAT} (N : MAP Γ (Fun B (Fun A C))) where
  module Coordinate = Permutation Γ A B
  diagram : MAP ((Γ × B) × A) C
  diagram = funUncurry (funUncurry N)
  square : MAP Γ (Fun (A × B) C)
  square = funCurry (diagram ∘ Coordinate.backward)
  module Curried = Currying.At 𝒯 M ℱ square

  raw : Curried.diagram =₁ diagram
  raw = comp-unitʳ diagram ∙ (diagram ◁ Coordinate.backward-forward) ∙
    comp-assoc Coordinate.J Coordinate.backward diagram ∙
    (funCurry-β (diagram ∘ Coordinate.backward) ▷ Coordinate.J)

  comparison : Curried.nested =₁ N
  comparison = funCurry-η N ∙
    funCurry-cong (funCurry-η (funUncurry N) ∙ funCurry-cong raw)
```
