# Postcomposing cocones

An extension of a cocone is compared with the original cocone after
postcomposition. The matching includes the associators on its two legs.
Postcomposition transports whole cocone comparisons, and an isomorphism
between two extensions supplies such a comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 public using (post-square)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; preWhisker-comp-at)

coconePost : {A B C D E : CAT} {u : MAP A B} {v : MAP A C} →
  MAP D E → Cocone u v D → Cocone u v E
coconePost {u = u} {v} F s = record
  { left = F ∘ Cocone.left s ; right = F ∘ Cocone.right s
  ; match = (comp-assoc v (Cocone.right s) F) ⁻¹ ∙
      ((F ◁ Cocone.match s) ∙ comp-assoc u (Cocone.left s) F) }

coconeIso-post : {A B C D E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cocone u v D} (F : MAP D E) → CoconeIso s t →
  CoconeIso (coconePost F s) (coconePost F t)
coconeIso-post {u = u} {v} {s} {t} F Φ = record
  { leftIso = F ◁ α ; rightIso = F ◁ β
  ; compatible = paste-squares (τs ∙ fs) (τt ∙ ft) (gs ⁻¹) (gt ⁻¹)
      first third last
      (paste-squares fs ft τs τt first second third
        (whisker-mixed-at α u F)
        (post-square F (Cocone.match s) (Cocone.match t) (α ▷ u) (β ▷ v)
          (CoconeIso.compatible Φ)))
      (move-square gt last third gs (whisker-mixed-at β v F)) }
  where
  α = CoconeIso.leftIso Φ
  β = CoconeIso.rightIso Φ
  fs = comp-assoc u (Cocone.left s) F
  ft = comp-assoc u (Cocone.left t) F
  gs = comp-assoc v (Cocone.right s) F
  gt = comp-assoc v (Cocone.right t) F
  τs = F ◁ Cocone.match s
  τt = F ◁ Cocone.match t
  first = (F ◁ α) ▷ u
  second = F ◁ (α ▷ u)
  third = F ◁ (β ▷ v)
  last = (F ◁ β) ▷ v

cocone-action : {A B C D E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v D) {F G : MAP D E} → F =₁ G →
  CoconeIso (coconePost F s) (coconePost G s)
cocone-action {u = u} {v} s {F} {G} δ = record
  { leftIso = δ ▷ p ; rightIso = δ ▷ q
  ; compatible = paste-squares (τF ∙ fF) (τG ∙ fG) (gF ⁻¹) (gG ⁻¹)
      first third last
      (paste-squares fF fG τF τG first second third
        (preWhisker-comp-at δ p u) ((interchange-at δ (Cocone.match s)) ⁻¹))
      (move-square gG last third gF (preWhisker-comp-at δ q v)) }
  where
  p = Cocone.left s
  q = Cocone.right s
  fF = comp-assoc u p F
  fG = comp-assoc u p G
  gF = comp-assoc v q F
  gG = comp-assoc v q G
  τF = F ◁ Cocone.match s
  τG = G ◁ Cocone.match s
  first = (δ ▷ p) ▷ u
  second = δ ▷ (p ∘ u)
  third = δ ▷ (q ∘ v)
  last = (δ ▷ q) ▷ v
```

