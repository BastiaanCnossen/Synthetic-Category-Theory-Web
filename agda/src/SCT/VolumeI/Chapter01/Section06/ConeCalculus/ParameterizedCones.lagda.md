# Adjoining a parameter to a cone

A cone on `Y` gives a cone on `X × Y`, with the parameter carried by
its left leg. Projection of this cone recovers restriction of the
original cone along the second projection. The projection witness is
the specified product beta comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedCones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (lift-base)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.LeftLifts 𝒯 using (module Left)

module Parameter (X : CAT) {C S T Y : CAT} {f : MAP C T} {p : MAP S T} (s : Cone f p Y) where
  l = Cone.left s
  r = Cone.right s
  R : MAP (X × Y) (X × C)
  R = productMap (id X) l
  β = pair-β₂ (id X ∘ pr₁ {C = X} {D = Y}) (l ∘ pr₂ {C = X} {D = Y})
  Z = comp-assoc (pr₂ {C = X} {D = Y}) r p
  d = Cone.match s ▷ pr₂ {C = X} {D = Y}
  A = comp-assoc (pr₂ {C = X} {D = Y}) l f
  κ = comp-assoc R (pr₂ {C = X} {D = C}) f
  rest = lift-base f (pr₂ {C = X} {D = C}) R β

  cone : Cone (f ∘ pr₂ {C = X}) p (X × Y)
  cone = record { left = R ; right = r ∘ pr₂
    ; match = Z ∙ (d ∙ ((A ⁻¹) ∙ rest)) }

  module Lift = Left (pr₂ {C = X} {D = C}) f (conePre (pr₂ {C = X} {D = Y}) s) R β

  abstract
    matching : Cone.match cone =₂ Cone.match Lift.value
    matching = (isoComp-assoc-at Z (d ∙ A ⁻¹) rest) ⁻¹ ∙
      isoComp-cong (idIso Z) ((isoComp-assoc-at d (A ⁻¹) rest) ⁻¹)

    projected-matching : Cone.match (compositeCone pr₂ f cone) =₂
      (Cone.match (conePre pr₂ s) ∙ (f ◁ β))
    projected-matching = Lift.matching ∙ isoComp-cong matching (idIso (κ ⁻¹))

  projection : ConeIso (compositeCone pr₂ f cone) (conePre pr₂ s)
  projection = record { leftIso = β ; rightIso = idIso (r ∘ pr₂)
    ; compatible = isoComp-cong ((postWhisker-idIso p (r ∘ pr₂)) ⁻¹)
        (idIso (Cone.match (compositeCone pr₂ f cone))) ∙
      ((isoComp-unitˡ-at (Cone.match (compositeCone pr₂ f cone))) ⁻¹ ∙ projected-matching ⁻¹) }
```
