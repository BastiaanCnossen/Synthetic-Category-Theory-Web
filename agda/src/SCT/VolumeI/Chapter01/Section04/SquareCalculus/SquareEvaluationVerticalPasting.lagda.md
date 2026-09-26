# Evaluating two vertically pasted squares

The first square changes the parameter of a diagram, and the second
changes its diagram shape. This calculation pastes the two squares before
or after evaluation. The two outer associators are part of the statement.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluationVerticalPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution 𝒯 M using (coordinate-outer-comp)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationMateCalculus 𝒯 using (append-four)

module At {A₀ A₁ B₀ B₁ D₀ D₁ C : CAT}
  (e : MAP D₁ C) (f : MAP A₀ A₁) (F : MAP B₀ B₁) (G : MAP D₀ D₁)
  (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₁) (y₀ : MAP B₀ D₀) (y₁ : MAP B₁ D₁)
  (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (β : (y₁ ∘ F) =₁ (G ∘ y₀)) where

  first = evaluate-square y₁ f F x₀ x₁ α
  composite-square = comp-assoc x₀ y₀ G ∙ ((β ▷ x₀) ∙ first)
  together = evaluate-square e f G (y₀ ∘ x₀) (y₁ ∘ x₁) composite-square
  inner = evaluate-square e F G y₀ y₁ β
  outer = evaluate-square (e ∘ y₁) f F x₀ x₁ α
  middle = evaluate-square e f (y₁ ∘ F) x₀ (y₁ ∘ x₁) first
  source-associator = comp-assoc x₁ y₁ e ▷ f
  target-associator = comp-assoc x₀ y₀ (e ∘ G)
  left-piece = comp-assoc y₀ G e ⁻¹ ▷ x₀
  middle-piece = (e ◁ β) ▷ x₀
  right-piece = comp-assoc F y₁ e ▷ x₀

  abstract
    expand : together =₂ (target-associator ∙ (left-piece ∙ (middle-piece ∙ middle)))
    expand = isoComp-cong (idIso target-associator)
        (isoComp-cong (idIso left-piece) (change-bottom e f x₀ (y₁ ∘ x₁) β first)) ∙
      associate-bottom e f y₀ G x₀ (y₁ ∘ x₁) ((β ▷ x₀) ∙ first)

    postcomposition : (middle ∙ source-associator) =₂ (right-piece ∙ outer)
    postcomposition = (coordinate-outer-comp x₀ F x₁ f α y₁ e) ⁻¹

    inner-image : (inner ▷ x₀) =₂ (left-piece ∙ (middle-piece ∙ right-piece))
    inner-image = isoComp-cong (idIso left-piece)
        (preWhisker-isoComp-at (e ◁ β) (comp-assoc F y₁ e) x₀) ∙
      preWhisker-isoComp-at ((comp-assoc y₀ G e) ⁻¹) ((e ◁ β) ∙ comp-assoc F y₁ e) x₀

    comparison : (together ∙ source-associator) =₂
      (target-associator ∙ ((inner ▷ x₀) ∙ outer))
    comparison = isoComp-cong (idIso target-associator)
        (isoComp-cong (inner-image ⁻¹) (idIso outer) ∙
        ((isoComp-assoc-at left-piece (middle-piece ∙ right-piece) outer) ⁻¹ ∙
          isoComp-cong (idIso left-piece) ((isoComp-assoc-at middle-piece right-piece outer) ⁻¹))) ∙
      (isoComp-cong (idIso target-associator)
        (isoComp-cong (idIso left-piece) (isoComp-cong (idIso middle-piece) postcomposition)) ∙
      (append-four target-associator left-piece middle-piece middle source-associator ∙
        isoComp-cong expand (idIso source-associator)))
```
