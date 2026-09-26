# Reading one coordinate of a cone

A commuting map of cospans reads a cone in one coordinate. Its comparison
and restriction laws retain the matching identification. We use this for
the two projections of a product square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)

module Coordinate {A B E A′ B′ E′ : CAT}
  (F : MAP A E) (G : MAP B E) (f : MAP A′ E′) (g : MAP B′ E′)
  (p : MAP A A′) (q : MAP B B′) (π : MAP E E′)
  (β : (π ∘ F) =₁ (f ∘ p)) (γ : (π ∘ G) =₁ (g ∘ q)) where

  left-normal : {T : CAT} (u : MAP T A) → (π ∘ (F ∘ u)) =₁ (f ∘ (p ∘ u))
  left-normal u = comp-assoc u p f ∙ ((β ▷ u) ∙ (comp-assoc u F π) ⁻¹)
  right-normal : {T : CAT} (v : MAP T B) → (π ∘ (G ∘ v)) =₁ (g ∘ (q ∘ v))
  right-normal v = comp-assoc v q g ∙ ((γ ▷ v) ∙ (comp-assoc v G π) ⁻¹)

  read : {T : CAT} → Cone F G T → Cone f g T
  read t = record { left = p ∘ Cone.left t ; right = q ∘ Cone.right t
    ; match = right-normal (Cone.right t) ∙
        ((π ◁ Cone.match t) ∙ (left-normal (Cone.left t)) ⁻¹) }

  left-natural : {T : CAT} {u v : MAP T A} (α : u =₁ v) →
    (left-normal v ∙ (π ◁ (F ◁ α))) =₂ ((f ◁ (p ◁ α)) ∙ left-normal u)
  left-natural {u = u} {v} α = paste-squares
    ((β ▷ u) ∙ (comp-assoc u F π) ⁻¹) ((β ▷ v) ∙ (comp-assoc v F π) ⁻¹)
    (comp-assoc u p f) (comp-assoc v p f)
    (π ◁ (F ◁ α)) ((f ∘ p) ◁ α) (f ◁ (p ◁ α))
    (substitution-square-projection π F (f ∘ p) β α) (postWhisker-comp-at α p f)

  right-natural : {T : CAT} {u v : MAP T B} (α : u =₁ v) →
    (right-normal v ∙ (π ◁ (G ◁ α))) =₂ ((g ◁ (q ◁ α)) ∙ right-normal u)
  right-natural {u = u} {v} α = paste-squares
    ((γ ▷ u) ∙ (comp-assoc u G π) ⁻¹) ((γ ▷ v) ∙ (comp-assoc v G π) ⁻¹)
    (comp-assoc u q g) (comp-assoc v q g)
    (π ◁ (G ◁ α)) ((g ∘ q) ◁ α) (g ◁ (q ◁ α))
    (substitution-square-projection π G (g ∘ q) γ α) (postWhisker-comp-at α q g)

  read-iso : {T : CAT} {s t : Cone F G T} → ConeIso s t → ConeIso (read s) (read t)
  read-iso {s = s} {t} Φ = record
    { leftIso = p ◁ ConeIso.leftIso Φ ; rightIso = q ◁ ConeIso.rightIso Φ
    ; compatible = transport-square
        (left-normal (Cone.left s)) (left-normal (Cone.left t))
        (right-normal (Cone.right s)) (right-normal (Cone.right t))
        (π ◁ Cone.match s) (π ◁ Cone.match t)
        (π ◁ (F ◁ ConeIso.leftIso Φ)) (π ◁ (G ◁ ConeIso.rightIso Φ))
        (f ◁ (p ◁ ConeIso.leftIso Φ)) (g ◁ (q ◁ ConeIso.rightIso Φ))
        (left-natural (ConeIso.leftIso Φ)) (right-natural (ConeIso.rightIso Φ))
        (post-square π (Cone.match s) (Cone.match t)
          (F ◁ ConeIso.leftIso Φ) (G ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ)) }

  read-pre : {S T : CAT} (r : MAP S T) (t : Cone F G T) →
    ConeIso (read (conePre r t)) (conePre r (read t))
  read-pre r t = record
    { leftIso = l ; rightIso = n
    ; compatible = normalize-cone-square AL AR δ δ′ (f ◁ l) (g ◁ n)
        (isoComp-assoc-at D (right-normal (v ∘ r))
          ((π ◁ Cone.match (conePre r t)) ∙ (left-normal (u ∘ r)) ⁻¹) ∙ calculation ⁻¹) }
    where
    u = Cone.left t
    v = Cone.right t
    l = (comp-assoc r u p) ⁻¹
    n = (comp-assoc r v q) ⁻¹
    AL = comp-assoc r (p ∘ u) f
    AR = comp-assoc r (q ∘ v) g
    L = AL ⁻¹ ∙ (f ◁ l)
    D = AR ⁻¹ ∙ (g ◁ n)
    δ = Cone.match (read t) ▷ r
    δ′ = Cone.match (read (conePre r t))
    calculation = coordinate-pre π t r (left-normal u) (right-normal v)
      (left-normal (u ∘ r)) (D ∙ right-normal (v ∘ r)) L
      (composite-normalization-pre π F p f β u r)
      (composite-normalization-pre π G q g γ v r)
```
