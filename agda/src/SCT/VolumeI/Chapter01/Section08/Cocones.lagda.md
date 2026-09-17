# Compatible cocones

A cocone retains its comparison on the common source. A comparison of
cocones retains the identification between the two resulting pastings.
These are the data tested when a square is mapped into another category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.Cocones
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right)

record Cocone {A B C : CAT} (u : MAP A B) (v : MAP A C) (E : CAT) : Set m where
  field
    left : MAP B E
    right : MAP C E
    match : =₁ (left ∘ u) (right ∘ v)

record CoconeIso {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s t : Cocone u v E) : Set m where
  field
    leftIso : =₁ (Cocone.left s) (Cocone.left t)
    rightIso : =₁ (Cocone.right s) (Cocone.right t)
    compatible : =₂ (Cocone.match t ∙ (leftIso ▷ u))
      ((rightIso ▷ v) ∙ Cocone.match s)

coconeIso-compose : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t w : Cocone u v E} → CoconeIso t w → CoconeIso s t → CoconeIso s w
coconeIso-compose {u = u} {v} {s} {t} {w} Ψ Φ = record
  { leftIso = CoconeIso.leftIso Ψ ∙ CoconeIso.leftIso Φ
  ; rightIso = CoconeIso.rightIso Ψ ∙ CoconeIso.rightIso Φ
  ; compatible =
      isoComp-cong (invIso (preWhisker-isoComp-at (CoconeIso.rightIso Ψ) (CoconeIso.rightIso Φ) v)) (idIso τs) ∙
      (invIso (isoComp-assoc-at β′ β τs) ∙
      (isoComp-cong (idIso β′) (CoconeIso.compatible Φ) ∙
      (isoComp-assoc-at β′ τt α ∙
      (isoComp-cong (CoconeIso.compatible Ψ) (idIso α) ∙
      (invIso (isoComp-assoc-at τw α′ α) ∙
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
  { leftIso = invIso (CoconeIso.leftIso Φ)
  ; rightIso = invIso (CoconeIso.rightIso Φ)
  ; compatible = isoComp-cong (invIso (pre-inverse (CoconeIso.rightIso Φ) v)) (idIso (Cocone.match t)) ∙
      (invIso (move-square (CoconeIso.rightIso Φ ▷ v) (Cocone.match s) (Cocone.match t)
        (CoconeIso.leftIso Φ ▷ u) (invIso (CoconeIso.compatible Φ))) ∙
        isoComp-cong (idIso (Cocone.match s)) (pre-inverse (CoconeIso.leftIso Φ) u)) }

coconeIso-adjust : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cocone u v E} (Φ : CoconeIso s t)
  (α : =₁ (Cocone.left s) (Cocone.left t)) (β : =₁ (Cocone.right s) (Cocone.right t)) →
  =₂ (CoconeIso.leftIso Φ) α → =₂ (CoconeIso.rightIso Φ) β → CoconeIso s t
coconeIso-adjust {u = u} {v} {s} {t} Φ α β l r = record
  { leftIso = α ; rightIso = β
  ; compatible = isoComp-cong (preWhisker v ◁ r) (idIso (Cocone.match s)) ∙
      (CoconeIso.compatible Φ ∙ isoComp-cong (idIso (Cocone.match t)) (preWhisker u ◁ invIso l)) }

coconeRetarget : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v E) (p : MAP B E) (q : MAP C E) →
  =₁ (Cocone.left s) p → =₁ (Cocone.right s) q → Cocone u v E
coconeRetarget {u = u} {v} s p q α β = record
  { left = p ; right = q ; match = (β ▷ v) ∙ (Cocone.match s ∙ invIso (α ▷ u)) }

coconeRetarget-β : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v E) (p : MAP B E) (q : MAP C E)
  (α : =₁ (Cocone.left s) p) (β : =₁ (Cocone.right s) q) →
  CoconeIso s (coconeRetarget s p q α β)
coconeRetarget-β {u = u} {v} s p q α β = record
  { leftIso = α ; rightIso = β
  ; compatible = isoComp-cong (idIso (β ▷ v))
      (isoComp-unitʳ-at (Cocone.match s) ∙
        (isoComp-cong (idIso (Cocone.match s)) (isoComp-inverseˡ-at (α ▷ u)) ∙
          isoComp-assoc-at (Cocone.match s) (invIso (α ▷ u)) (α ▷ u))) ∙
      isoComp-assoc-at (β ▷ v) (Cocone.match s ∙ invIso (α ▷ u)) (α ▷ u) }

cocone-match-change : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (p : MAP B E) (q : MAP C E) (σ τ : =₁ (p ∘ u) (q ∘ v)) →
  =₂ σ τ → CoconeIso (record { left = p ; right = q ; match = σ })
    (record { left = p ; right = q ; match = τ })
cocone-match-change {u = u} {v} p q σ τ δ = record
  { leftIso = idIso p ; rightIso = idIso q
  ; compatible = isoComp-cong (invIso (preWhisker-idIso q v)) (idIso σ) ∙
      (invIso (isoComp-unitˡ-at σ) ∙
      (invIso δ ∙
      (isoComp-unitʳ-at τ ∙ isoComp-cong (idIso τ) (preWhisker-idIso p u)))) }
```
