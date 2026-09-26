# Restricting one arrow of a cocone

A specified identification of the upper span arrow changes the cocone
matching. Comparisons can be transported and reflected through this change.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeArrowRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

restrict : {A B C E : CAT} {u u′ : MAP A B} {v : MAP A C} →
  u =₁ u′ → Cocone u′ v E → Cocone u v E
restrict α s = record
  { left = Cocone.left s ; right = Cocone.right s
  ; match = Cocone.match s ∙ (Cocone.left s ◁ α) }

restrict-iso : {A B C E : CAT} {u u′ : MAP A B} {v : MAP A C}
  (α : u =₁ u′) {s t : Cocone u′ v E} →
  CoconeIso s t → CoconeIso (restrict α s) (restrict α t)
restrict-iso {u = u} {u′} {v} α {s} {t} Φ = record
  { leftIso = δ ; rightIso = CoconeIso.rightIso Φ
  ; compatible = isoComp-assoc-at R τs P ∙
      (isoComp-cong (CoconeIso.compatible Φ) (idIso P) ∙
      ((isoComp-assoc-at τt (δ ▷ u′) P) ⁻¹ ∙
      (isoComp-cong (idIso τt) ((interchange-at δ α) ⁻¹) ∙
        isoComp-assoc-at τt Q (δ ▷ u)))) }
  where
  δ = CoconeIso.leftIso Φ
  R = CoconeIso.rightIso Φ ▷ v
  P = Cocone.left s ◁ α
  Q = Cocone.left t ◁ α
  τs = Cocone.match s
  τt = Cocone.match t

reflect-iso : {A B C E : CAT} {u u′ : MAP A B} {v : MAP A C}
  (α : u =₁ u′) (s t : Cocone u′ v E) →
  CoconeIso (restrict α s) (restrict α t) → CoconeIso s t
reflect-iso {u = u} {u′} {v} α s t Φ = record
  { leftIso = δ ; rightIso = CoconeIso.rightIso Φ
  ; compatible = cancel-right-reflect P
      ((isoComp-assoc-at R τs P) ⁻¹ ∙
      (CoconeIso.compatible Φ ∙
      ((isoComp-assoc-at τt Q (δ ▷ u)) ⁻¹ ∙
      (isoComp-cong (idIso τt) (interchange-at δ α) ∙
        isoComp-assoc-at τt (δ ▷ u′) P)))) }
  where
  δ = CoconeIso.leftIso Φ
  R = CoconeIso.rightIso Φ ▷ v
  P = Cocone.left s ◁ α
  Q = Cocone.left t ◁ α
  τs = Cocone.match s
  τt = Cocone.match t

postcomparison : {A B C D E : CAT} {u u′ : MAP A B} {v : MAP A C}
  (α : u =₁ u′) (F : MAP D E) (s : Cocone u′ v D) →
  CoconeIso (restrict α (coconePost F s)) (coconePost F (restrict α s))
postcomparison {u = u} {u′} {v} α F s = cocone-match-change _ _ _ _ matching
  where
  p = Cocone.left s
  q = Cocone.right s
  τ = Cocone.match s
  b = comp-assoc v q F
  t = F ◁ τ
  A = comp-assoc u p F
  B = comp-assoc u′ p F
  H = F ◁ (p ◁ α)
  K = (F ∘ p) ◁ α
  matching : ((b ⁻¹ ∙ (t ∙ B)) ∙ K) =₂
    (b ⁻¹ ∙ ((F ◁ (τ ∙ (p ◁ α))) ∙ A))
  matching = isoComp-cong (idIso (b ⁻¹))
    (isoComp-cong ((postWhisker-isoComp-at F τ (p ◁ α)) ⁻¹) (idIso A) ∙
      (isoComp-assoc-at t H A) ⁻¹) ∙
    (isoComp-cong (idIso (b ⁻¹))
      (isoComp-cong (idIso t) (postWhisker-comp-at α p F) ∙
        isoComp-assoc-at t B K) ∙ isoComp-assoc-at (b ⁻¹) (t ∙ B) K)
```
