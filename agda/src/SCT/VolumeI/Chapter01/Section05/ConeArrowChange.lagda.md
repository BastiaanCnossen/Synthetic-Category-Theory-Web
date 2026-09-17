# Changing a cospan arrow

A specified natural isomorphism changes the corresponding boundary of a
cone. The inverse and restriction comparisons keep that isomorphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section05.ConeArrowChange
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯 public
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-right)
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)

changeLeft : {C D E T : CAT} {f f′ : MAP C E} {g : MAP D E} →
  =₁ f f′ → Cone f g T → Cone f′ g T
changeLeft α s = record
  { left = Cone.left s ; right = Cone.right s
  ; match = Cone.match s ∙ invIso (α ▷ Cone.left s) }

changeLeft-iso : {C D E T : CAT} {f f′ : MAP C E} {g : MAP D E}
  (α : =₁ f f′) {s t : Cone f g T} → ConeIso s t → ConeIso (changeLeft α s) (changeLeft α t)
changeLeft-iso {f = f} {f′} {g} α {s} {t} Φ = record
  { leftIso = ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
  ; compatible = isoComp-assoc-at (g ◁ ConeIso.rightIso Φ) (Cone.match s) (invIso As) ∙
      (isoComp-cong (ConeIso.compatible Φ) (idIso (invIso As)) ∙
      (invIso (isoComp-assoc-at (Cone.match t) (f ◁ δ) (invIso As)) ∙
      (isoComp-cong (idIso (Cone.match t))
        (move-square At (f ◁ δ) (f′ ◁ δ) As (interchange-at α δ)) ∙
        isoComp-assoc-at (Cone.match t) (invIso At) (f′ ◁ δ)))) }
  where
  δ = ConeIso.leftIso Φ
  As = α ▷ Cone.left s
  At = α ▷ Cone.left t

changeLeft-back : {C D E T : CAT} {f f′ : MAP C E} {g : MAP D E}
  (α : =₁ f f′) (s : Cone f g T) → ConeIso (changeLeft (invIso α) (changeLeft α s)) s
changeLeft-back α s = cone-match-change _ _ _ _
  (isoComp-unitʳ-at τ ∙
    (isoComp-cong (idIso τ) (isoComp-inverseˡ-at δ) ∙
    (isoComp-assoc-at τ (invIso δ) δ ∙
      isoComp-cong (idIso (τ ∙ invIso δ)) (inverse-inverse δ ∙ (isoInv ◁ pre-inverse α p)))))
  where
  p = Cone.left s
  τ = Cone.match s
  δ = α ▷ p

changeLeft-backʳ : {C D E T : CAT} {f f′ : MAP C E} {g : MAP D E}
  (α : =₁ f f′) (s : Cone f′ g T) → ConeIso (changeLeft α (changeLeft (invIso α) s)) s
changeLeft-backʳ α s = cone-match-change _ _ _ _
  (cancel-right δ τ ∙
    isoComp-cong (isoComp-cong (idIso τ) (inverse-inverse δ ∙ (isoInv ◁ pre-inverse α p)))
      (idIso (invIso δ)))
  where
  p = Cone.left s
  τ = Cone.match s
  δ = α ▷ p

changeLeft-pre : {C D E R T : CAT} {f f′ : MAP C E} {g : MAP D E}
  (α : =₁ f f′) (r : MAP R T) (s : Cone f g T) →
  ConeIso (conePre r (changeLeft α s)) (changeLeft α (conePre r s))
changeLeft-pre {f = f} {f′} {g} α r s = record
  { leftIso = idIso (p ∘ r) ; rightIso = idIso (q ∘ r)
  ; compatible = isoComp-cong (invIso (postWhisker-idIso g (q ∘ r))) (idIso source) ∙
      (invIso (isoComp-unitˡ-at source) ∙
      (step₉ ∙ (step₈ ∙ (step₇ ∙ (step₆ ∙ (step₅ ∙ (step₄ ∙ (step₃ ∙ (step₂ ∙
        (step₁ ∙ isoComp-cong (idIso (K ∙ invIso E)) (postWhisker-idIso f′ (p ∘ r)))))))))))) }
  where
  p = Cone.left s
  q = Cone.right s
  τ = Cone.match s
  A = α ▷ p
  B = comp-assoc r p f′
  D = comp-assoc r p f
  E = α ▷ (p ∘ r)
  G = idIso (f′ ∘ (p ∘ r))
  H = comp-assoc r q g
  u = τ ▷ r
  K = H ∙ (u ∙ invIso D)
  source = Cone.match (conePre r (changeLeft α s))
  step₁ = isoComp-assoc-at K (invIso E) G
  step₂ = isoComp-cong (idIso K)
    (move-square E D G (B ∙ (A ▷ r))
      (invIso (isoComp-unitˡ-at (B ∙ (A ▷ r))) ∙ invIso (preWhisker-comp-at α p r)))
  step₃ = invIso (isoComp-assoc-at K D (invIso (B ∙ (A ▷ r))))
  cancelD = isoComp-unitʳ-at u ∙
    (isoComp-cong (idIso u) (isoComp-inverseˡ-at D) ∙ isoComp-assoc-at u (invIso D) D)
  step₄ = isoComp-cong
    (isoComp-cong (idIso H) cancelD ∙ isoComp-assoc-at H (u ∙ invIso D) D)
    (idIso (invIso (B ∙ (A ▷ r))))
  step₅ = isoComp-assoc-at H u (invIso (B ∙ (A ▷ r)))
  step₆ = isoComp-cong (idIso H) (isoComp-cong (idIso u) (inverse-composite B (A ▷ r)))
  step₇ = isoComp-cong (idIso H) (invIso (isoComp-assoc-at u (invIso (A ▷ r)) (invIso B)))
  step₈ = isoComp-cong (idIso H)
    (isoComp-cong (isoComp-cong (idIso u) (invIso (pre-inverse A r))) (idIso (invIso B)))
  step₉ = isoComp-cong (idIso H)
    (isoComp-cong (invIso (preWhisker-isoComp-at τ (invIso A) r)) (idIso (invIso B)))
```
