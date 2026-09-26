# Evaluation along a square of split projections

A square between two chosen sections induces a comparison between the
corresponding evaluations. Its first projection equation supplies all
coherence needed below; the section witnesses remain specified.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯
  using (compose-base; lift-base; lift-compose; lift-square; Square)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M using (evaluate-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-comp-at; preWhisker-id-at)

abstract
  section-natural : {X K C : CAT} (π : MAP K X) (i : MAP X K)
    (b : (π ∘ i) =₁ (id X)) {h k : MAP X C} (η : h =₁ k) →
    (section-image π i b k ∙ ((η ▷ π) ▷ i)) =₂
      (η ∙ section-image π i b h)
  section-natural π i b {h} {k} η =
    paste-squares (lift-base h π i b) (lift-base k π i b)
      (comp-unitʳ h) (comp-unitʳ k) ((η ▷ π) ▷ i) (η ▷ id _) η
      (paste-squares (comp-assoc i π h) (comp-assoc i π k)
        (h ◁ b) (k ◁ b) ((η ▷ π) ▷ i) (η ▷ (π ∘ i)) (η ▷ id _)
        (preWhisker-comp-at η π i) ((interchange-at η b) ⁻¹))
      (preWhisker-id-at η)

module Along {X Y K L C : CAT}
  (π : MAP L Y) (ρ : MAP K X) (i : MAP X K) (j : MAP Y L)
  (bi : (ρ ∘ i) =₁ (id X)) (bj : (π ∘ j) =₁ (id Y))
  (r : MAP X Y) (R : MAP K L) (bR : (π ∘ R) =₁ (r ∘ ρ))
  (α : (j ∘ r) =₁ (R ∘ i))
  (square : Square π (compose-base π j bj r (comp-unitˡ r))
    (compose-base π R bR i (section-image ρ i bi r)) α)
  (h : MAP Y C) where
  A = comp-assoc ρ r h
  B = lift-base h π R bR
  D = A ⁻¹ ∙ B
  E = evaluate-square (h ∘ π) r R i j α
  Si = section-image ρ i bi (h ∘ r)
  Sj = section-image π j bj h
  outgoing = compose-base π R bR i (section-image ρ i bi r)
  incoming = compose-base π j bj r (comp-unitˡ r)
  T = comp-assoc i R (h ∘ π)
  U = comp-assoc r j (h ∘ π)

  abstract
    section-cancel : (Si ∙ (A ⁻¹ ▷ i)) =₂
      (lift-base h (r ∘ ρ) i (section-image ρ i bi r))
    section-cancel = cancel-right (A ▷ i) _ ∙
      isoComp-cong (section-comp ρ i bi r h) (pre-inverse A i)

    output-left : (Si ∙ (D ▷ i)) =₂
      (lift-base h (r ∘ ρ) i (section-image ρ i bi r) ∙ (B ▷ i))
    output-left = isoComp-cong section-cancel (idIso (B ▷ i)) ∙
      ((isoComp-assoc-at Si (A ⁻¹ ▷ i) (B ▷ i)) ⁻¹ ∙
        isoComp-cong (idIso Si) (preWhisker-isoComp-at (A ⁻¹) B i))

    output-right : (lift-base h π (R ∘ i) outgoing ∙ T) =₂
      (lift-base h (r ∘ ρ) i (section-image ρ i bi r) ∙ (B ▷ i))
    output-right = isoComp-cong (idIso _) (cancel-inverse-tail (B ▷ i) T) ∙
      (isoComp-assoc-at _ ((B ▷ i) ∙ T ⁻¹) T ∙
        isoComp-cong ((lift-compose h π R i bR (section-image ρ i bi r)) ⁻¹) (idIso T))

    output-normal : (Si ∙ (D ▷ i)) =₂
      (lift-base h π (R ∘ i) outgoing ∙ T)
    output-normal = output-right ⁻¹ ∙ output-left

    comparison : ((Si ∙ (D ▷ i)) ∙ E) =₂ (Sj ▷ r)
    comparison = cancel-inverse-tail (Sj ▷ r) U ∙
      (isoComp-cong (isoComp-unitˡ-at _ ∙ (section-pre π j bj r h) ⁻¹) (idIso U) ∙
      (isoComp-cong (lift-square h π incoming outgoing α square) (idIso U) ∙
      ((isoComp-assoc-at _ ((h ∘ π) ◁ α) U) ⁻¹ ∙
      (isoComp-cong (idIso _) (cancel-inverse T (((h ∘ π) ◁ α) ∙ U)) ∙
      (isoComp-assoc-at _ T E ∙ isoComp-cong output-normal (idIso E))))))
```
