# Currying a framed transformation

An interval diagram between two uncurried functors can be curried after
interchanging its interval and domain coordinates. Reflection of the
endpoint identifications gives the specified original functors as its
endpoints. The reflected identifications retain their uncurried images.
The inverse comparison with expression uncurrying is a separate result.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates as Coordinates
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingInsertion as Insertion

module Curry {Γ X C : CAT} (f g : MAP Γ (Fun X C))
  (α : MorphismExpression (funUncurry f) (funUncurry g)) where
  private module A = MorphismExpression α
  module Coordinate = Coordinates.Coordinates 𝒯 M ℱ Γ X [1]
    using (parameter; inner; outer; module Vertical)

  pair-domain : MAP ((Γ × [1]) × X) (Γ × X)
  pair-domain = pair Coordinate.parameter Coordinate.inner
  permutation : MAP ((Γ × [1]) × X) ((Γ × X) × [1])
  permutation = pair pair-domain Coordinate.outer
  original : MAP ((Γ × X) × [1]) C
  original = funUncurry A.arrow
  diagram : MAP ((Γ × [1]) × X) C
  diagram = original ∘ permutation
  first-curry : MAP (Γ × [1]) (Fun X C)
  first-curry = funCurry diagram
  arrow : MAP Γ (Ar (Fun X C))
  arrow = funCurry first-curry

  module Endpoint (z : Obj-abs [1]) (h : MAP Γ (Fun X C))
    (frame : (evaluate z ∘ A.arrow) =₁ funUncurry h) where
    module Restriction = Coordinate.Vertical z
      using (step; parameter-step; inner-step; outer-step)
    step = Restriction.step

    domain-comparison : (pair-domain ∘ step) =₁ id (Γ × X)
    domain-comparison = pair-projections ∙
      (pair-cong Restriction.parameter-step Restriction.inner-step ∙
        pair-pre Coordinate.parameter Coordinate.inner step)

    insertion-comparison : (permutation ∘ step) =₁ insert {X = Γ × X} z
    insertion-comparison = Insertion.At.Endpoint.comparison 𝒯 M ℱ I Γ X z

    raw : funUncurry (first-curry ∘ insert z) =₁ funUncurry h
    raw = (frame ∙ (evaluate-uncurry z A.arrow) ⁻¹) ∙
      ((original ◁ insertion-comparison) ∙
        (comp-assoc step permutation original ∙
          ((funCurry-β diagram ▷ step) ∙ funUncurry-restrict first-curry (insert z))))

    abstract
      reflected : (first-curry ∘ insert z) =₁ h
      reflected = funIsoReflect _ _ raw

      reflected-image : funUncurryIso reflected =₂ raw
      reflected-image = funIsoReflect-β _ _ raw

    comparison : (evaluate z ∘ arrow) =₁ h
    comparison = reflected ∙ evaluate-curry z first-curry

  module Source = Endpoint zero f A.source-frame
  module Target = Endpoint one g A.target-frame

  value : MorphismExpression f g
  value = record
    { arrow = arrow
    ; source-frame = Source.comparison
    ; target-frame = Target.comparison }
```
