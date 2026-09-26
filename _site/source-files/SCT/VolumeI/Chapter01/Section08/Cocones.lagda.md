# Compatible cocones

A cocone retains its comparison on the common source. A comparison of
cocones retains the identification between the two resulting pastings.
These are the data tested when a square is mapped into another category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.Cocones
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right)

record Cocone {A B C : CAT} (u : MAP A B) (v : MAP A C) (E : CAT) : Set m where
  field
    left : MAP B E
    right : MAP C E
    match : (left ∘ u) =₁ (right ∘ v)

record CoconeIso {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s t : Cocone u v E) : Set m where
  field
    leftIso : (Cocone.left s) =₁ (Cocone.left t)
    rightIso : (Cocone.right s) =₁ (Cocone.right t)
    compatible : (Cocone.match t ∙ (leftIso ▷ u)) =₂
      ((rightIso ▷ v) ∙ Cocone.match s)

coconeIso-compose : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t w : Cocone u v E} → CoconeIso t w → CoconeIso s t → CoconeIso s w
coconeIso-compose {u = u} {v} {s} {t} {w} Ψ Φ = record
  { leftIso = CoconeIso.leftIso Ψ ∙ CoconeIso.leftIso Φ
  ; rightIso = CoconeIso.rightIso Ψ ∙ CoconeIso.rightIso Φ
  ; compatible =
      isoComp-cong ((preWhisker-isoComp-at (CoconeIso.rightIso Ψ) (CoconeIso.rightIso Φ) v) ⁻¹) (idIso τs) ∙
      ((isoComp-assoc-at β′ β τs) ⁻¹ ∙
      (isoComp-cong (idIso β′) (CoconeIso.compatible Φ) ∙
      (isoComp-assoc-at β′ τt α ∙
      (isoComp-cong (CoconeIso.compatible Ψ) (idIso α) ∙
      ((isoComp-assoc-at τw α′ α) ⁻¹ ∙
        isoComp-cong (idIso τw) (preWhisker-isoComp-at (CoconeIso.leftIso Ψ) (CoconeIso.leftIso Φ) u)))))) }
  where
  τs = Cocone.match s
  τt = Cocone.match t
  τw = Cocone.match w
  α = CoconeIso.leftIso Φ ▷ u
  α′ = CoconeIso.leftIso Ψ ▷ u
  β = CoconeIso.rightIso Φ ▷ v
  β′ = CoconeIso.rightIso Ψ ▷ v

coconeIso-inverse : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cocone u v E} → CoconeIso s t → CoconeIso t s
coconeIso-inverse {u = u} {v} {s} {t} Φ = record
  { leftIso = (CoconeIso.leftIso Φ) ⁻¹
  ; rightIso = (CoconeIso.rightIso Φ) ⁻¹
  ; compatible = isoComp-cong ((pre-inverse (CoconeIso.rightIso Φ) v) ⁻¹) (idIso (Cocone.match t)) ∙
      ((move-square (CoconeIso.rightIso Φ ▷ v) (Cocone.match s) (Cocone.match t)
        (CoconeIso.leftIso Φ ▷ u) ((CoconeIso.compatible Φ) ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso (Cocone.match s)) (pre-inverse (CoconeIso.leftIso Φ) u)) }

coconeIso-adjust : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cocone u v E} (Φ : CoconeIso s t)
  (α : (Cocone.left s) =₁ (Cocone.left t)) (β : (Cocone.right s) =₁ (Cocone.right t)) →
  (CoconeIso.leftIso Φ) =₂ α → (CoconeIso.rightIso Φ) =₂ β → CoconeIso s t
coconeIso-adjust {u = u} {v} {s} {t} Φ α β l r = record
  { leftIso = α ; rightIso = β
  ; compatible = isoComp-cong (preWhisker v ◁ r) (idIso (Cocone.match s)) ∙
      (CoconeIso.compatible Φ ∙ isoComp-cong (idIso (Cocone.match t)) (preWhisker u ◁ l ⁻¹)) }

coconeRetarget : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v E) (p : MAP B E) (q : MAP C E) →
  (Cocone.left s) =₁ p → (Cocone.right s) =₁ q → Cocone u v E
coconeRetarget {u = u} {v} s p q α β = record
  { left = p ; right = q ; match = (β ▷ v) ∙ (Cocone.match s ∙ (α ▷ u) ⁻¹) }

coconeRetarget-β : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v E) (p : MAP B E) (q : MAP C E)
  (α : (Cocone.left s) =₁ p) (β : (Cocone.right s) =₁ q) →
  CoconeIso s (coconeRetarget s p q α β)
coconeRetarget-β {u = u} {v} s p q α β = record
  { leftIso = α ; rightIso = β
  ; compatible = isoComp-cong (idIso (β ▷ v))
      (isoComp-unitʳ-at (Cocone.match s) ∙
        (isoComp-cong (idIso (Cocone.match s)) (isoComp-inverseˡ-at (α ▷ u)) ∙
          isoComp-assoc-at (Cocone.match s) ((α ▷ u) ⁻¹) (α ▷ u))) ∙
      isoComp-assoc-at (β ▷ v) (Cocone.match s ∙ (α ▷ u) ⁻¹) (α ▷ u) }

cocone-match-change : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (p : MAP B E) (q : MAP C E) (σ τ : (p ∘ u) =₁ (q ∘ v)) →
  σ =₂ τ → CoconeIso (record { left = p ; right = q ; match = σ })
    (record { left = p ; right = q ; match = τ })
cocone-match-change {u = u} {v} p q σ τ δ = record
  { leftIso = idIso p ; rightIso = idIso q
  ; compatible = isoComp-cong ((preWhisker-idIso q v) ⁻¹) (idIso σ) ∙
      ((isoComp-unitˡ-at σ) ⁻¹ ∙
      (δ ⁻¹ ∙
      (isoComp-unitʳ-at τ ∙ isoComp-cong (idIso τ) (preWhisker-idIso p u)))) }
```
