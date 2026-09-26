# Reversing the cocone restriction bridge

The reverse bridge is the expanded pasting used by the naturality
comparison for a composite functor. This calculation connects that
existing choice to the compact cube comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeBridgeReversal
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; inverse-composite)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction 𝒯 using (module Bridge)

module Reversal {A B A′ B′ E : CAT} (u : MAP A B) (u′ : MAP A′ B′)
  (i : MAP A A′) (j : MAP B B′) (α : (u′ ∘ i) =₁ (j ∘ u)) (f : MAP B′ E) where
  module B = Bridge u u′ i j α
  inside = comp-assoc i u′ f
  outside = comp-assoc u j f
  expanded = outside ⁻¹ ∙ ((f ◁ α) ∙ inside)

  abstract
    comparison : (B.value f) ⁻¹ =₂ expanded
    comparison = isoComp-assoc-at (outside ⁻¹) (f ◁ α) inside ∙
      (isoComp-cong
        (isoComp-cong (idIso (outside ⁻¹)) (inverse-inverse (f ◁ α) ∙ (＝-inv ◁ post-inverse f α)))
        (inverse-inverse inside) ∙
        (isoComp-cong (inverse-composite (f ◁ α ⁻¹) outside) (idIso ((inside ⁻¹) ⁻¹)) ∙
          inverse-composite (inside ⁻¹) ((f ◁ α ⁻¹) ∙ outside)))
```
