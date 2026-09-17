# Reversing a cone

Swapping the legs also inverts the matching isomorphism. The restriction
comparison records how inversion interacts with the two associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.ConeSymmetry
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeRestriction 𝒯 public
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

cone-match-change : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (p : MAP T C) (q : MAP T D) (τ τ′ : NatIso (f ∘ p) (g ∘ q)) → Iso₂ τ τ′ →
  ConeIso (record { left = p ; right = q ; match = τ })
          (record { left = p ; right = q ; match = τ′ })
cone-match-change {f = f} {g} p q τ τ′ κ = record
  { leftIso = idIso p ; rightIso = idIso q
  ; compatible = isoComp-cong (invIso (postWhisker-idIso g q)) (idIso τ) ∙
      (invIso (isoComp-unitˡ-at τ) ∙
      (invIso κ ∙ (isoComp-unitʳ-at τ′ ∙
        isoComp-cong (idIso τ′) (postWhisker-idIso f p)))) }

coneSwap : {C D E T : CAT} {f : MAP C E} {g : MAP D E} → Cone f g T → Cone g f T
coneSwap s = record
  { left = Cone.right s ; right = Cone.left s ; match = invIso (Cone.match s) }

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
  (invIso expanded ∙ isoComp-cong (idIso B)
    (isoComp-cong (pre-inverse τ r) (idIso (invIso A))))
  where
  A = comp-assoc r (Cone.right s) g
  B = comp-assoc r (Cone.left s) f
  τ = Cone.match s
  u = τ ▷ r
  expanded = isoComp-assoc-at B (invIso u) (invIso A) ∙
    (isoComp-cong (isoComp-cong (inverse-inverse B) (idIso (invIso u))) (idIso (invIso A)) ∙
    (isoComp-cong (inverse-composite u (invIso B)) (idIso (invIso A)) ∙
      inverse-composite A (u ∙ invIso B)))
```
