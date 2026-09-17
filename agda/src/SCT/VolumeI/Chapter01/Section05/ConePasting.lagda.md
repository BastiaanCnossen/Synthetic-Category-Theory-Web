# Pasting cone diagrams

Pasting retains the matching isomorphism of each square. The comparison
calculus below is used for the chosen pullback pasting equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.ConePasting
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.CompositeCones 𝒯 public
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module PasteCones {A B X Z Q : CAT} (f : MAP A B) (g : MAP B Z) {h : MAP X Z}
  (t : Cone g h Q) where

  u = Cone.left t
  v = Cone.right t

  flatten : {T : CAT} → Cone f u T → Cone (g ∘ f) h T
  flatten s = record
    { left = Cone.left s ; right = v ∘ Cone.right s
    ; match = Cone.match (conePre (Cone.right s) t) ∙
        ((g ◁ Cone.match s) ∙ comp-assoc (Cone.left s) f g) }

  flatten-match : {T : CAT} (s : Cone f u T) →
    =₂ (Cone.match (compositeCone f g (flatten s)))
      (Cone.match (conePre (Cone.right s) t) ∙ (g ◁ Cone.match s))
  flatten-match s = cancel-right assocLeft (ν ∙ ρ) ∙
    isoComp-cong (invIso (isoComp-assoc-at ν ρ assocLeft)) (idIso (invIso assocLeft))
    where
    assocLeft = comp-assoc (Cone.left s) f g
    ν = Cone.match (conePre (Cone.right s) t)
    ρ = g ◁ Cone.match s

  flatten-composite : {T : CAT} (s : Cone f u T) →
    ConeIso (compositeCone f g (flatten s)) (conePre (Cone.right s) t)
  flatten-composite s = record
    { leftIso = Cone.match s ; rightIso = idIso (v ∘ Cone.right s)
    ; compatible = isoComp-cong (invIso (postWhisker-idIso h (v ∘ Cone.right s))) (idIso σ) ∙
        (invIso (isoComp-unitˡ-at σ) ∙ invIso (flatten-match s)) }
    where
    σ = Cone.match (compositeCone f g (flatten s))

  flatten-iso : {T : CAT} {s s′ : Cone f u T} → ConeIso s s′ → ConeIso (flatten s) (flatten s′)
  flatten-iso {s = s} {s′} Φ = compositeCone-compatible f g (flatten s) (flatten s′) α (v ◁ β)
    (isoComp-cong (idIso (h ◁ (v ◁ β))) (invIso (flatten-match s)) ∙
    (isoComp-assoc-at (h ◁ (v ◁ β)) ν ρ ∙
    (isoComp-cong (ConeIso.compatible (cone-action t β)) (idIso ρ) ∙
    (invIso (isoComp-assoc-at ν′ (g ◁ (u ◁ β)) ρ) ∙
    (isoComp-cong (idIso ν′) (postWhisker-isoComp-at g (u ◁ β) (Cone.match s)) ∙
    (isoComp-cong (idIso ν′) (postWhisker g ◁ ConeIso.compatible Φ) ∙
    (isoComp-cong (idIso ν′) (invIso (postWhisker-isoComp-at g (Cone.match s′) (f ◁ α))) ∙
    (isoComp-assoc-at ν′ ρ′ (g ◁ (f ◁ α)) ∙
      isoComp-cong (flatten-match s′) (idIso (g ◁ (f ◁ α)))))))))))
    where
    α = ConeIso.leftIso Φ
    β = ConeIso.rightIso Φ
    ν = Cone.match (conePre (Cone.right s) t)
    ν′ = Cone.match (conePre (Cone.right s′) t)
    ρ = g ◁ Cone.match s
    ρ′ = g ◁ Cone.match s′

  flatten-pre : {S T : CAT} (r : MAP S T) (s : Cone f u T) →
    ConeIso (conePre r (flatten s)) (flatten (conePre r s))
  flatten-pre r s = compositeCone-compatible f g _ _ (idIso (p ∘ r)) assocRight
    (ConeIso.compatible normalized)
    where
    p = Cone.left s
    q = Cone.right s
    assocRight = comp-assoc r q v
    matchRestricted = Cone.match (conePre r s)
    raw = coneIso-compose (coneIso-inverse (flatten-composite (conePre r s)))
      (coneIso-compose (conePre-assoc r q t)
      (coneIso-compose (coneIso-pre r (flatten-composite s))
        (coneIso-inverse (compositeCone-pre f g r (flatten s)))))
    left-normal = invIso (postWhisker-idIso f (p ∘ r)) ∙ isoComp-inverseˡ-at matchRestricted
    right-normal = isoComp-unitˡ-at assocRight ∙
      isoComp-cong (inverse-identity (v ∘ (q ∘ r)))
        (isoComp-unitʳ-at assocRight ∙
          isoComp-cong (idIso assocRight)
            (isoComp-unitˡ-at (idIso ((v ∘ q) ∘ r)) ∙
              isoComp-cong (preWhisker-idIso (v ∘ q) r) (inverse-identity ((v ∘ q) ∘ r))))
    normalized = coneIso-adjust raw (f ◁ idIso (p ∘ r)) assocRight left-normal right-normal
```
