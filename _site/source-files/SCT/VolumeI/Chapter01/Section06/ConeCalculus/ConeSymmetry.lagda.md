# Reversing a cone

Swapping the legs also inverts the matching isomorphism. The restriction
comparison records how inversion interacts with the two associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

cone-match-change : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (p : MAP T C) (q : MAP T D) (τ τ′ : (f ∘ p) =₁ (g ∘ q)) → τ =₂ τ′ →
  ConeIso (record { left = p ; right = q ; match = τ })
          (record { left = p ; right = q ; match = τ′ })
cone-match-change {f = f} {g} p q τ τ′ κ = record
  { leftIso = idIso p ; rightIso = idIso q
  ; compatible = isoComp-cong ((postWhisker-idIso g q) ⁻¹) (idIso τ) ∙
      ((isoComp-unitˡ-at τ) ⁻¹ ∙
      (κ ⁻¹ ∙ (isoComp-unitʳ-at τ′ ∙
        isoComp-cong (idIso τ′) (postWhisker-idIso f p)))) }

coneSwap : {C D E T : CAT} {f : MAP C E} {g : MAP D E} → Cone f g T → Cone g f T
coneSwap s = record
  { left = Cone.right s ; right = Cone.left s ; match = (Cone.match s) ⁻¹ }

coneIso-swap : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} → ConeIso s t → ConeIso (coneSwap s) (coneSwap t)
coneIso-swap {f = f} {g} {s} {t} Φ = record
  { leftIso = ConeIso.rightIso Φ ; rightIso = ConeIso.leftIso Φ
  ; compatible = move-square (Cone.match t) (f ◁ ConeIso.leftIso Φ)
      (g ◁ ConeIso.rightIso Φ) (Cone.match s) (ConeIso.compatible Φ) }

coneSwap-swap : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → ConeIso (coneSwap (coneSwap s)) s
coneSwap-swap s = cone-match-change _ _ _ _ (inverse-inverse (Cone.match s))

coneSwap-pre : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP S T) (s : Cone f g T) →
  ConeIso (conePre r (coneSwap s)) (coneSwap (conePre r s))
coneSwap-pre {f = f} {g} r s = cone-match-change _ _ _ _
  (expanded ⁻¹ ∙ isoComp-cong (idIso B)
    (isoComp-cong (pre-inverse τ r) (idIso (A ⁻¹))))
  where
  A = comp-assoc r (Cone.right s) g
  B = comp-assoc r (Cone.left s) f
  τ = Cone.match s
  u = τ ▷ r
  expanded = isoComp-assoc-at B (u ⁻¹) (A ⁻¹) ∙
    (isoComp-cong (isoComp-cong (inverse-inverse B) (idIso (u ⁻¹))) (idIso (A ⁻¹)) ∙
    (isoComp-cong (inverse-composite u (B ⁻¹)) (idIso (A ⁻¹)) ∙
      inverse-composite A (u ∙ B ⁻¹)))
```
