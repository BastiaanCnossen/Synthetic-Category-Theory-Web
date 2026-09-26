# Cocones specified by two endpoint frames

Two arrows into one specified object give a matching by taking the
quotient of their endpoint identifications. Comparisons of the frames
and postcomposition preserve this matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.FramedCocones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.CoconeAssociativity 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (quotient-square)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)

framed-cocone : {A B C D : CAT} {u : MAP A B} {v : MAP A C}
  (p : MAP B D) (q : MAP C D) {z : MAP A D} →
  (p ∘ u) =₁ z → (q ∘ v) =₁ z → Cocone u v D
framed-cocone p q α β = record { left = p ; right = q ; match = β ⁻¹ ∙ α }

framed-comparison : {A B C D : CAT} {u : MAP A B} {v : MAP A C}
  {p p′ : MAP B D} {q q′ : MAP C D} {z : MAP A D}
  (α : (p ∘ u) =₁ z) (β : (q ∘ v) =₁ z)
  (α′ : (p′ ∘ u) =₁ z) (β′ : (q′ ∘ v) =₁ z)
  (l : p =₁ p′) (r : q =₁ q′) →
  (α′ ∙ (l ▷ u)) =₂ α → (β′ ∙ (r ▷ v)) =₂ β →
  CoconeIso (framed-cocone p q α β) (framed-cocone p′ q′ α′ β′)
framed-comparison {u = u} {v} {z = z} α β α′ β′ l r first second = record
  { leftIso = l ; rightIso = r
  ; compatible = quotient-square α β α′ β′ (l ▷ u) (r ▷ v) (idIso z)
      ((isoComp-unitˡ-at α) ⁻¹ ∙ first) ((isoComp-unitˡ-at β) ⁻¹ ∙ second) }

module PostFrame {A B C D E : CAT} {u : MAP A B} {v : MAP A C}
  (F : MAP D E) (p : MAP B D) (q : MAP C D) {z : MAP A D}
  (α : (p ∘ u) =₁ z) (β : (q ∘ v) =₁ z) where
  left-frame = (F ◁ α) ∙ comp-assoc u p F
  right-frame = (F ◁ β) ∙ comp-assoc v q F
  source-cocone = coconePost F (framed-cocone p q α β)
  target-cocone = framed-cocone (F ∘ p) (F ∘ q) left-frame right-frame
  assoc-left = comp-assoc u p F
  assoc-right = comp-assoc v q F

  abstract
    normalize : (Cocone.match source-cocone) =₂ (Cocone.match target-cocone)
    normalize = isoComp-cong ((inverse-composite (F ◁ β) assoc-right) ⁻¹) (idIso left-frame) ∙
      ((isoComp-assoc-at (assoc-right ⁻¹) ((F ◁ β) ⁻¹) left-frame) ⁻¹ ∙
      (isoComp-cong (idIso (assoc-right ⁻¹))
        (isoComp-assoc-at ((F ◁ β) ⁻¹) (F ◁ α) assoc-left) ∙
      (isoComp-cong (idIso (assoc-right ⁻¹))
        (isoComp-cong (isoComp-cong (post-inverse F β) (idIso (F ◁ α))) (idIso assoc-left)) ∙
        isoComp-cong (idIso (assoc-right ⁻¹))
          (isoComp-cong (postWhisker-isoComp-at F (β ⁻¹) α) (idIso assoc-left)))))

  comparison : CoconeIso source-cocone target-cocone
  comparison = cocone-match-change (F ∘ p) (F ∘ q)
    (Cocone.match source-cocone) (Cocone.match target-cocone) normalize

module PostFramedComparison {A B C D E H : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v D) (σ : MAP D E) (F : MAP E H)
  (p : MAP B E) (q : MAP C E) {z : MAP A E}
  (α : (p ∘ u) =₁ z) (β : (q ∘ v) =₁ z)
  (Φ : CoconeIso (coconePost σ s) (framed-cocone p q α β)) where
  module Frames = PostFrame F p q α β
  left-edge = (F ◁ CoconeIso.leftIso Φ) ∙ comp-assoc (Cocone.left s) σ F
  right-edge = (F ◁ CoconeIso.rightIso Φ) ∙ comp-assoc (Cocone.right s) σ F
  together = coconeIso-compose (coconeIso-post F Φ) (coconePost-assoc F σ s)
  raw = coconeIso-compose Frames.comparison together

  comparison : CoconeIso (coconePost (F ∘ σ) s) Frames.target-cocone
  comparison = coconeIso-adjust raw left-edge right-edge
    (isoComp-unitˡ-at left-edge) (isoComp-unitˡ-at right-edge)
```
