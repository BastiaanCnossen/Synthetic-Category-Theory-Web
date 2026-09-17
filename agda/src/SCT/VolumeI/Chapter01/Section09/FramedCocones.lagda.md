# Cocones specified by two endpoint frames

Two arrows into one specified object give a matching by taking the
quotient of their endpoint identifications. Comparisons of the frames
and postcomposition preserve this matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)

module SCT.VolumeI.Chapter01.Section09.FramedCocones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section09.CoconeAssociativity 𝒯 public
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯 using (quotient-square)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (inverse-composite)

framed-cocone : {A B C D : CAT} {u : MAP A B} {v : MAP A C}
  (p : MAP B D) (q : MAP C D) {z : MAP A D} →
  =₁ (p ∘ u) z → =₁ (q ∘ v) z → Cocone u v D
framed-cocone p q α β = record { left = p ; right = q ; match = invIso β ∙ α }

framed-comparison : {A B C D : CAT} {u : MAP A B} {v : MAP A C}
  {p p′ : MAP B D} {q q′ : MAP C D} {z : MAP A D}
  (α : =₁ (p ∘ u) z) (β : =₁ (q ∘ v) z)
  (α′ : =₁ (p′ ∘ u) z) (β′ : =₁ (q′ ∘ v) z)
  (l : =₁ p p′) (r : =₁ q q′) →
  =₂ (α′ ∙ (l ▷ u)) α → =₂ (β′ ∙ (r ▷ v)) β →
  CoconeIso (framed-cocone p q α β) (framed-cocone p′ q′ α′ β′)
framed-comparison {u = u} {v} {z = z} α β α′ β′ l r first second = record
  { leftIso = l ; rightIso = r
  ; compatible = quotient-square α β α′ β′ (l ▷ u) (r ▷ v) (idIso z)
      (invIso (isoComp-unitˡ-at α) ∙ first) (invIso (isoComp-unitˡ-at β) ∙ second) }

module PostFrame {A B C D E : CAT} {u : MAP A B} {v : MAP A C}
  (F : MAP D E) (p : MAP B D) (q : MAP C D) {z : MAP A D}
  (α : =₁ (p ∘ u) z) (β : =₁ (q ∘ v) z) where
  left-frame = (F ◁ α) ∙ comp-assoc u p F
  right-frame = (F ◁ β) ∙ comp-assoc v q F
  source-cocone = coconePost F (framed-cocone p q α β)
  target-cocone = framed-cocone (F ∘ p) (F ∘ q) left-frame right-frame
  assoc-left = comp-assoc u p F
  assoc-right = comp-assoc v q F

  abstract
    normalize : =₂ (Cocone.match source-cocone) (Cocone.match target-cocone)
    normalize = isoComp-cong (invIso (inverse-composite (F ◁ β) assoc-right)) (idIso left-frame) ∙
      (invIso (isoComp-assoc-at (invIso assoc-right) (invIso (F ◁ β)) left-frame) ∙
      (isoComp-cong (idIso (invIso assoc-right))
        (isoComp-assoc-at (invIso (F ◁ β)) (F ◁ α) assoc-left) ∙
      (isoComp-cong (idIso (invIso assoc-right))
        (isoComp-cong (isoComp-cong (post-inverse F β) (idIso (F ◁ α))) (idIso assoc-left)) ∙
        isoComp-cong (idIso (invIso assoc-right))
          (isoComp-cong (postWhisker-isoComp-at F (invIso β) α) (idIso assoc-left)))))

  comparison : CoconeIso source-cocone target-cocone
  comparison = cocone-match-change (F ∘ p) (F ∘ q)
    (Cocone.match source-cocone) (Cocone.match target-cocone) normalize

module PostFramedComparison {A B C D E H : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v D) (σ : MAP D E) (F : MAP E H)
  (p : MAP B E) (q : MAP C E) {z : MAP A E}
  (α : =₁ (p ∘ u) z) (β : =₁ (q ∘ v) z)
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
