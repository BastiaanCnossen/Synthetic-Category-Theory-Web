# Cones over a composite

An outer cone for a composite base functor determines a cone for its
second factor. This is the first operation in the proof of the pasting
lemma. Its action on comparisons keeps the associators at both endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IP
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PU

module SCT.VolumeI.Chapter01.Section06.CompositeCones
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeRestriction 𝒯 public
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)
open IP vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (pentagon-whiskered)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

compositeCone : {A B X Z T : CAT} (f : MAP A B) (g : MAP B Z) {h : MAP X Z} →
  Cone (g ∘ f) h T → Cone g h T
compositeCone f g s = record
  { left = f ∘ Cone.left s ; right = Cone.right s
  ; match = Cone.match s ∙ (comp-assoc (Cone.left s) f g) ⁻¹ }

compositeConeIso : {A B X Z T : CAT} (f : MAP A B) (g : MAP B Z) {h : MAP X Z}
  {s t : Cone (g ∘ f) h T} → ConeIso s t → ConeIso (compositeCone f g s) (compositeCone f g t)
compositeConeIso f g {h} {s} {t} Φ = record
  { leftIso = f ◁ ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
  ; compatible = isoComp-assoc-at (h ◁ ConeIso.rightIso Φ) (Cone.match s) (As ⁻¹) ∙
      (isoComp-cong (ConeIso.compatible Φ) (idIso (As ⁻¹)) ∙
      ((isoComp-assoc-at (Cone.match t) ((g ∘ f) ◁ α) (As ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso (Cone.match t))
        (move-square At ((g ∘ f) ◁ α) (g ◁ (f ◁ α)) As (postWhisker-comp-at α f g)) ∙
        isoComp-assoc-at (Cone.match t) (At ⁻¹) (g ◁ (f ◁ α))))) }
  where
  α = ConeIso.leftIso Φ
  As = comp-assoc (Cone.left s) f g
  At = comp-assoc (Cone.left t) f g

compositeCone-compatible : {A B X Z T : CAT} (f : MAP A B) (g : MAP B Z) {h : MAP X Z}
  (s t : Cone (g ∘ f) h T) (α : (Cone.left s) =₁ (Cone.left t))
  (β : (Cone.right s) =₁ (Cone.right t)) →
  (Cone.match (compositeCone f g t) ∙ (g ◁ (f ◁ α))) =₂
    ((h ◁ β) ∙ Cone.match (compositeCone f g s)) → ConeIso s t
compositeCone-compatible f g {h} s t α β κ = record
  { leftIso = α ; rightIso = β
  ; compatible = cancel-right-reflect (As ⁻¹)
      ((isoComp-assoc-at (h ◁ β) (Cone.match s) (As ⁻¹)) ⁻¹ ∙
      (κ ∙ ((isoComp-assoc-at (Cone.match t) (At ⁻¹) (g ◁ (f ◁ α))) ⁻¹ ∙
      (isoComp-cong (idIso (Cone.match t))
        ((move-square At ((g ∘ f) ◁ α) (g ◁ (f ◁ α)) As (postWhisker-comp-at α f g)) ⁻¹) ∙
        isoComp-assoc-at (Cone.match t) ((g ∘ f) ◁ α) (As ⁻¹))))) }
  where
  As = comp-assoc (Cone.left s) f g
  At = comp-assoc (Cone.left t) f g

compositeCone-pre : {A B X Z R T : CAT} (f : MAP A B) (g : MAP B Z) {h : MAP X Z}
  (r : MAP R T) (s : Cone (g ∘ f) h T) →
  ConeIso (conePre r (compositeCone f g s)) (compositeCone f g (conePre r s))
compositeCone-pre f g {h} r s = record
  { leftIso = comp-assoc r p f ; rightIso = idIso (q ∘ r)
  ; compatible = isoComp-cong ((postWhisker-idIso h (q ∘ r)) ⁻¹) (idIso source) ∙
      ((isoComp-unitˡ-at source) ⁻¹ ∙
      (step₉ ∙ (step₈ ∙ (step₇ ∙ (step₆ ∙ (step₅ ∙ (step₄ ∙ (step₃ ∙ (step₂ ∙ step₁))))))))) }
  where
  p = Cone.left s
  q = Cone.right s
  τ = Cone.match s
  A = comp-assoc p f g
  B = comp-assoc r (f ∘ p) g
  D = comp-assoc r p (g ∘ f)
  E = comp-assoc (p ∘ r) f g
  G = g ◁ comp-assoc r p f
  H = comp-assoc r q h
  u = τ ▷ r
  K = H ∙ (u ∙ D ⁻¹)
  source = Cone.match (conePre r (compositeCone f g s))
  step₁ = isoComp-assoc-at K (E ⁻¹) G
  step₂ = isoComp-cong (idIso K)
    (move-square E D G (B ∙ (A ▷ r)) (pentagon-whiskered r p f g))
  step₃ = (isoComp-assoc-at K D ((B ∙ (A ▷ r)) ⁻¹)) ⁻¹
  cancelD = isoComp-unitʳ-at u ∙
    (isoComp-cong (idIso u) (isoComp-inverseˡ-at D) ∙ isoComp-assoc-at u (D ⁻¹) D)
  step₄ = isoComp-cong
    (isoComp-cong (idIso H) cancelD ∙ isoComp-assoc-at H (u ∙ D ⁻¹) D)
    (idIso ((B ∙ (A ▷ r)) ⁻¹))
  step₅ = isoComp-assoc-at H u ((B ∙ (A ▷ r)) ⁻¹)
  step₆ = isoComp-cong (idIso H) (isoComp-cong (idIso u) (inverse-composite B (A ▷ r)))
  step₇ = isoComp-cong (idIso H) ((isoComp-assoc-at u ((A ▷ r) ⁻¹) (B ⁻¹)) ⁻¹)
  step₈ = isoComp-cong (idIso H)
    (isoComp-cong (isoComp-cong (idIso u) ((pre-inverse A r) ⁻¹)) (idIso (B ⁻¹)))
  step₉ = isoComp-cong (idIso H)
    (isoComp-cong ((preWhisker-isoComp-at τ (A ⁻¹) r) ⁻¹) (idIso (B ⁻¹)))
```
