# Composing and inverting cone comparisons

The matching proofs use the finite vertical composition laws and
whiskering preservation. No uniqueness of compatibility witnesses is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section05.ConeCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯 public
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right)

coneIso-compose : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t u : Cone f g T} → ConeIso t u → ConeIso s t → ConeIso s u
coneIso-compose {f = f} {g} {s} {t} {u} Ψ Φ = record
  { leftIso = ConeIso.leftIso Ψ ∙ ConeIso.leftIso Φ
  ; rightIso = ConeIso.rightIso Ψ ∙ ConeIso.rightIso Φ
  ; compatible =
      isoComp-cong (invIso (postWhisker-isoComp-at g (ConeIso.rightIso Ψ) (ConeIso.rightIso Φ))) (idIso τs) ∙
      (invIso (isoComp-assoc-at gβ′ gβ τs) ∙
      (isoComp-cong (idIso gβ′) (ConeIso.compatible Φ) ∙
      (isoComp-assoc-at gβ′ τt fα ∙
      (isoComp-cong (ConeIso.compatible Ψ) (idIso fα) ∙
      (invIso (isoComp-assoc-at τu fα′ fα) ∙
        isoComp-cong (idIso τu) (postWhisker-isoComp-at f (ConeIso.leftIso Ψ) (ConeIso.leftIso Φ))))))) }
  where
  τs = Cone.match s
  τt = Cone.match t
  τu = Cone.match u
  fα = f ◁ ConeIso.leftIso Φ
  fα′ = f ◁ ConeIso.leftIso Ψ
  gβ = g ◁ ConeIso.rightIso Φ
  gβ′ = g ◁ ConeIso.rightIso Ψ

coneIso-inverse : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} → ConeIso s t → ConeIso t s
coneIso-inverse {f = f} {g} {s} {t} Φ = record
  { leftIso = invIso (ConeIso.leftIso Φ)
  ; rightIso = invIso (ConeIso.rightIso Φ)
  ; compatible =
      isoComp-cong (invIso (post-inverse g (ConeIso.rightIso Φ))) (idIso (Cone.match t)) ∙
      (invIso (move-square (g ◁ ConeIso.rightIso Φ) (Cone.match s) (Cone.match t)
        (f ◁ ConeIso.leftIso Φ) (invIso (ConeIso.compatible Φ))) ∙
        isoComp-cong (idIso (Cone.match s)) (post-inverse f (ConeIso.leftIso Φ))) }

coneIso-adjust : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} (Φ : ConeIso s t)
  (α : =₁ (Cone.left s) (Cone.left t)) (β : =₁ (Cone.right s) (Cone.right t)) →
  =₂ (ConeIso.leftIso Φ) α → =₂ (ConeIso.rightIso Φ) β → ConeIso s t
coneIso-adjust {f = f} {g} {s} {t} Φ α β l r = record
  { leftIso = α ; rightIso = β
  ; compatible = isoComp-cong (postWhisker g ◁ r) (idIso (Cone.match s)) ∙
      (ConeIso.compatible Φ ∙ isoComp-cong (idIso (Cone.match t)) (postWhisker f ◁ invIso l)) }

coneRetarget : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (p : MAP T C) (q : MAP T D) →
  =₁ (Cone.left s) p → =₁ (Cone.right s) q → Cone f g T
coneRetarget {f = f} {g} s p q α β = record
  { left = p ; right = q ; match = (g ◁ β) ∙ (Cone.match s ∙ invIso (f ◁ α)) }

coneRetarget-β : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (p : MAP T C) (q : MAP T D)
  (α : =₁ (Cone.left s) p) (β : =₁ (Cone.right s) q) →
  ConeIso s (coneRetarget s p q α β)
coneRetarget-β {f = f} {g} s p q α β = record
  { leftIso = α ; rightIso = β
  ; compatible = isoComp-cong (idIso (g ◁ β))
      (isoComp-unitʳ-at (Cone.match s) ∙
        (isoComp-cong (idIso (Cone.match s)) (isoComp-inverseˡ-at (f ◁ α)) ∙
          isoComp-assoc-at (Cone.match s) (invIso (f ◁ α)) (f ◁ α))) ∙
      isoComp-assoc-at (g ◁ β) (Cone.match s ∙ invIso (f ◁ α)) (f ◁ α) }

coneRetarget-match : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} (Φ : ConeIso s t)
  → =₂ (Cone.match (coneRetarget s (Cone.left t) (Cone.right t)
      (ConeIso.leftIso Φ) (ConeIso.rightIso Φ))) (Cone.match t)
coneRetarget-match {f = f} {g} {s} {t} Φ = invIso
  (isoComp-assoc-at (g ◁ ConeIso.rightIso Φ) (Cone.match s) (invIso (f ◁ ConeIso.leftIso Φ)) ∙
  (isoComp-cong (ConeIso.compatible Φ) (idIso (invIso (f ◁ ConeIso.leftIso Φ))) ∙
    invIso (cancel-right (f ◁ ConeIso.leftIso Φ) (Cone.match t))))
```
