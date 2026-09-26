# Restricting a cocone along a map of spans

A map of spans has two specified squares. Restriction uses both squares
and the original cocone matching. The bridge comparison below isolates
the reassociation on either leg; its naturality proves that restriction
carries whole cocone comparisons to whole cocone comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module Bridge {A B A′ B′ : CAT} (u : MAP A B) (u′ : MAP A′ B′)
  (i : MAP A A′) (j : MAP B B′) (α : (u′ ∘ i) =₁ (j ∘ u)) where
  value : {E : CAT} (f : MAP B′ E) → ((f ∘ j) ∘ u) =₁ ((f ∘ u′) ∘ i)
  value f = (comp-assoc i u′ f) ⁻¹ ∙ ((f ◁ α ⁻¹) ∙ comp-assoc u j f)

  abstract
    natural : {E : CAT} {f g : MAP B′ E} (δ : f =₁ g) →
      (value g ∙ ((δ ▷ j) ▷ u)) =₂ (((δ ▷ u′) ▷ i) ∙ value f)
    natural {f = f} {g} δ = paste-squares
      ((f ◁ α ⁻¹) ∙ comp-assoc u j f) ((g ◁ α ⁻¹) ∙ comp-assoc u j g)
      ((comp-assoc i u′ f) ⁻¹) ((comp-assoc i u′ g) ⁻¹)
      ((δ ▷ j) ▷ u) (δ ▷ (u′ ∘ i)) ((δ ▷ u′) ▷ i)
      (paste-squares (comp-assoc u j f) (comp-assoc u j g) (f ◁ α ⁻¹) (g ◁ α ⁻¹)
        ((δ ▷ j) ▷ u) (δ ▷ (j ∘ u)) (δ ▷ (u′ ∘ i))
        (preWhisker-comp-at δ j u) ((interchange-at δ (α ⁻¹)) ⁻¹))
      (move-square (comp-assoc i u′ g) ((δ ▷ u′) ▷ i) (δ ▷ (u′ ∘ i))
        (comp-assoc i u′ f) (preWhisker-comp-at δ u′ i))

module Restriction {A B C A′ B′ C′ : CAT}
  (u : MAP A B) (v : MAP A C) (u′ : MAP A′ B′) (v′ : MAP A′ C′)
  (i : MAP A A′) (j : MAP B B′) (k : MAP C C′)
  (α : (u′ ∘ i) =₁ (j ∘ u)) (β : (v′ ∘ i) =₁ (k ∘ v)) where
  module Left = Bridge u u′ i j α
  module Right = Bridge v v′ i k β

  value : {E : CAT} → Cocone u′ v′ E → Cocone u v E
  value s = record
    { left = Cocone.left s ∘ j ; right = Cocone.right s ∘ k
    ; match = (Right.value (Cocone.right s)) ⁻¹ ∙
        ((Cocone.match s ▷ i) ∙ Left.value (Cocone.left s)) }

  abstract
    comparison : {E : CAT} {s t : Cocone u′ v′ E} → CoconeIso s t → CoconeIso (value s) (value t)
    comparison {s = s} {t} Φ = record
      { leftIso = δ ▷ j ; rightIso = ε ▷ k
      ; compatible = paste-squares ((Cocone.match s ▷ i) ∙ L₀) ((Cocone.match t ▷ i) ∙ L₁)
          (R₀ ⁻¹) (R₁ ⁻¹) ((δ ▷ j) ▷ u) ((ε ▷ v′) ▷ i) ((ε ▷ k) ▷ v)
          (paste-squares L₀ L₁ (Cocone.match s ▷ i) (Cocone.match t ▷ i)
            ((δ ▷ j) ▷ u) ((δ ▷ u′) ▷ i) ((ε ▷ v′) ▷ i) (Left.natural δ)
            (preWhisker-isoComp-at (ε ▷ v′) (Cocone.match s) i ∙
              ((preWhisker i ◁ CoconeIso.compatible Φ) ∙
                (preWhisker-isoComp-at (Cocone.match t) (δ ▷ u′) i) ⁻¹)))
          (move-square R₁ ((ε ▷ k) ▷ v) ((ε ▷ v′) ▷ i) R₀ (Right.natural ε)) }
      where
      δ : Cocone.left s =₁ Cocone.left t
      δ = CoconeIso.leftIso Φ
      ε : Cocone.right s =₁ Cocone.right t
      ε = CoconeIso.rightIso Φ
      L₀ : ((Cocone.left s ∘ j) ∘ u) =₁ ((Cocone.left s ∘ u′) ∘ i)
      L₀ = Left.value (Cocone.left s)
      L₁ : ((Cocone.left t ∘ j) ∘ u) =₁ ((Cocone.left t ∘ u′) ∘ i)
      L₁ = Left.value (Cocone.left t)
      R₀ : ((Cocone.right s ∘ k) ∘ v) =₁ ((Cocone.right s ∘ v′) ∘ i)
      R₀ = Right.value (Cocone.right s)
      R₁ : ((Cocone.right t ∘ k) ∘ v) =₁ ((Cocone.right t ∘ v′) ∘ i)
      R₁ = Right.value (Cocone.right t)
```
