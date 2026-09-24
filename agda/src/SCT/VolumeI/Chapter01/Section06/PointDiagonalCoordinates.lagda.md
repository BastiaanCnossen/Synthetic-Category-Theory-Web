# Coordinates of a diagonal square over two points

The two legs of the recovered fiber cone have the same map to the terminal
category. Terminal uniqueness identifies their comparison witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as Pairing

module SCT.VolumeI.Chapter01.Section06.PointDiagonalCoordinates
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯
  using (transport-square; reflect-transport-square; post-square; decode-encode)
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection; move-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; postWhisker-id-at)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality)

module Coordinates {E : CAT} (f g : Obj-abs E) where

  F = pair f g
  Δ = pair (id E) (id E)

  left₁ : {T : CAT} (u : MAP T One) → (pr₁ ∘ (F ∘ u)) =₁ (f ∘ u)
  left₁ u = project-pair₁ f g u
  left₂ : {T : CAT} (u : MAP T One) → (pr₂ ∘ (F ∘ u)) =₁ (g ∘ u)
  left₂ u = project-pair₂ f g u
  right₁ : {T : CAT} (v : MAP T E) → (pr₁ ∘ (Δ ∘ v)) =₁ v
  right₁ v = comp-unitˡ v ∙ project-pair₁ (id E) (id E) v
  right₂ : {T : CAT} (v : MAP T E) → (pr₂ ∘ (Δ ∘ v)) =₁ v
  right₂ v = comp-unitˡ v ∙ project-pair₂ (id E) (id E) v

  edge₁ : {T : CAT} (t : Cone F Δ T) → (f ∘ Cone.left t) =₁ (Cone.right t)
  edge₁ t = right₁ (Cone.right t) ∙ ((pr₁ ◁ Cone.match t) ∙ (left₁ (Cone.left t)) ⁻¹)
  edge₂ : {T : CAT} (t : Cone F Δ T) → (g ∘ Cone.left t) =₁ (Cone.right t)
  edge₂ t = right₂ (Cone.right t) ∙ ((pr₂ ◁ Cone.match t) ∙ (left₂ (Cone.left t)) ⁻¹)

  from : {T : CAT} → Cone F Δ T → Cone f g T
  from t = record { left = Cone.left t ; right = Cone.left t
                  ; match = (edge₂ t) ⁻¹ ∙ edge₁ t }

  opaque
    left₁-natural : {T : CAT} {u u′ : MAP T One} (L : u =₁ u′)
      → (left₁ u′ ∙ (pr₁ ◁ (F ◁ L))) =₂ ((f ◁ L) ∙ left₁ u)
    left₁-natural {u = u} {u′} L =
      substitution-square-projection pr₁ F f (pair-β₁ f g) L

    left₂-natural : {T : CAT} {u u′ : MAP T One} (L : u =₁ u′)
      → (left₂ u′ ∙ (pr₂ ◁ (F ◁ L))) =₂ ((g ◁ L) ∙ left₂ u)
    left₂-natural {u = u} {u′} L =
      substitution-square-projection pr₂ F g (pair-β₂ f g) L

    right₁-natural : {T : CAT} {v v′ : MAP T E} (R : v =₁ v′)
      → (right₁ v′ ∙ (pr₁ ◁ (Δ ◁ R))) =₂ (R ∙ right₁ v)
    right₁-natural {v = v} {v′} R = paste-squares
      (project-pair₁ (id E) (id E) v) (project-pair₁ (id E) (id E) v′)
      (comp-unitˡ v) (comp-unitˡ v′) (pr₁ ◁ (Δ ◁ R)) (id E ◁ R) R
      (substitution-square-projection pr₁ Δ (id E) (pair-β₁ (id E) (id E)) R)
      (postWhisker-id-at R)

    right₂-natural : {T : CAT} {v v′ : MAP T E} (R : v =₁ v′)
      → (right₂ v′ ∙ (pr₂ ◁ (Δ ◁ R))) =₂ (R ∙ right₂ v)
    right₂-natural {v = v} {v′} R = paste-squares
      (project-pair₂ (id E) (id E) v) (project-pair₂ (id E) (id E) v′)
      (comp-unitˡ v) (comp-unitˡ v′) (pr₂ ◁ (Δ ◁ R)) (id E ◁ R) R
      (substitution-square-projection pr₂ Δ (id E) (pair-β₂ (id E) (id E)) R)
      (postWhisker-id-at R)

  opaque
    coordinate₁ : {T : CAT} {s t : Cone F Δ T} (Φ : ConeIso s t)
      → (edge₁ t ∙ (f ◁ ConeIso.leftIso Φ)) =₂ (ConeIso.rightIso Φ ∙ edge₁ s)
    coordinate₁ {s = s} {t} Φ = transport-square
      (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
      (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
      (pr₁ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₁ ◁ (Δ ◁ ConeIso.rightIso Φ))
      (f ◁ ConeIso.leftIso Φ) (ConeIso.rightIso Φ)
      (left₁-natural (ConeIso.leftIso Φ)) (right₁-natural (ConeIso.rightIso Φ))
      (post-square pr₁ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (Δ ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

    coordinate₂ : {T : CAT} {s t : Cone F Δ T} (Φ : ConeIso s t)
      → (edge₂ t ∙ (g ◁ ConeIso.leftIso Φ)) =₂ (ConeIso.rightIso Φ ∙ edge₂ s)
    coordinate₂ {s = s} {t} Φ = transport-square
      (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
      (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
      (pr₂ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₂ ◁ (Δ ◁ ConeIso.rightIso Φ))
      (g ◁ ConeIso.leftIso Φ) (ConeIso.rightIso Φ)
      (left₂-natural (ConeIso.leftIso Φ)) (right₂-natural (ConeIso.rightIso Φ))
      (post-square pr₂ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (Δ ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

  cone-from-coordinates : {T : CAT} (s t : Cone F Δ T)
    (L : (Cone.left s) =₁ (Cone.left t)) (R : (Cone.right s) =₁ (Cone.right t))
    → (edge₁ t ∙ (f ◁ L)) =₂ (R ∙ edge₁ s)
    → (edge₂ t ∙ (g ◁ L)) =₂ (R ∙ edge₂ s)
    → ConeIso s t
  cone-from-coordinates s t L R e₁ e₂ = record
    { leftIso = L ; rightIso = R
    ; compatible = pair-iso-extensionality
      ((postWhisker-isoComp-at pr₁ (Δ ◁ R) (Cone.match s)) ⁻¹ ∙
      (reflect-transport-square
        (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
        (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t) (pr₁ ◁ (F ◁ L)) (pr₁ ◁ (Δ ◁ R))
        (f ◁ L) R (left₁-natural L) (right₁-natural R) e₁ ∙
        postWhisker-isoComp-at pr₁ (Cone.match t) (F ◁ L)))
      ((postWhisker-isoComp-at pr₂ (Δ ◁ R) (Cone.match s)) ⁻¹ ∙
      (reflect-transport-square
        (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
        (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t) (pr₂ ◁ (F ◁ L)) (pr₂ ◁ (Δ ◁ R))
        (g ◁ L) R (left₂-natural L) (right₂-natural R) e₂ ∙
        postWhisker-isoComp-at pr₂ (Cone.match t) (F ◁ L))) }

  from-iso : {T : CAT} {s t : Cone F Δ T} → ConeIso s t → ConeIso (from s) (from t)
  from-iso {s = s} {t} Φ = record
    { leftIso = ConeIso.leftIso Φ ; rightIso = ConeIso.leftIso Φ
    ; compatible = isoComp-assoc-at (g ◁ ConeIso.leftIso Φ) ((edge₂ s) ⁻¹) (edge₁ s) ∙
      (isoComp-cong (move-square (edge₂ t) (g ◁ ConeIso.leftIso Φ) (ConeIso.rightIso Φ) (edge₂ s) (coordinate₂ Φ)) (idIso (edge₁ s)) ∙
      ((isoComp-assoc-at ((edge₂ t) ⁻¹) (ConeIso.rightIso Φ) (edge₁ s)) ⁻¹ ∙
      (isoComp-cong (idIso ((edge₂ t) ⁻¹)) (coordinate₁ Φ) ∙
        isoComp-assoc-at ((edge₂ t) ⁻¹) (edge₁ t) (f ◁ ConeIso.leftIso Φ)))) }

```

Recovery also reflects the existence of a cone comparison. Terminal uniqueness
identifies its two recovered leg comparisons; the second coordinate determines
its right leg.
The first coordinate equation is precisely the recovered compatibility.

```agda
  from-reflect : {T : CAT} {s t : Cone F Δ T} → ConeIso (from s) (from t) → ConeIso s t
  from-reflect {s = s} {t} Φ = cone-from-coordinates s t L R first second
    where
    L = ConeIso.leftIso Φ
    l = ConeIso.leftIso Φ
    r = ConeIso.rightIso Φ
    agree : r =₂ l
    agree = equiv-reflect (terminalIso-isEquiv _ _) r l (terminal-iso _ _)
    compatibility : ((edge₂ t) ⁻¹ ∙ edge₁ t) ∙ (f ◁ l) =₂
      ((g ◁ l) ∙ ((edge₂ s) ⁻¹ ∙ edge₁ s))
    compatibility = isoComp-cong (postWhisker g ◁ agree) (idIso ((edge₂ s) ⁻¹ ∙ edge₁ s)) ∙ ConeIso.compatible Φ
    R : (Cone.right s) =₁ (Cone.right t)
    R = edge₂ t ∙ ((g ◁ l) ∙ (edge₂ s) ⁻¹)
    first : (edge₁ t ∙ (f ◁ l)) =₂ (R ∙ edge₁ s)
    first = (isoComp-assoc-at (edge₂ t) ((g ◁ l) ∙ (edge₂ s) ⁻¹) (edge₁ s)) ⁻¹ ∙
      (isoComp-cong (idIso (edge₂ t)) ((isoComp-assoc-at (g ◁ l) ((edge₂ s) ⁻¹) (edge₁ s)) ⁻¹) ∙
      (isoComp-cong (idIso (edge₂ t)) compatibility ∙
      (isoComp-assoc-at (edge₂ t) ((edge₂ t) ⁻¹ ∙ edge₁ t) (f ◁ l) ∙
        isoComp-cong ((cancel-inverse (edge₂ t) (edge₁ t)) ⁻¹) (idIso (f ◁ l)))))
    second : (edge₂ t ∙ (g ◁ l)) =₂ (R ∙ edge₂ s)
    second = (isoComp-assoc-at (edge₂ t) ((g ◁ l) ∙ (edge₂ s) ⁻¹) (edge₂ s)) ⁻¹ ∙
      isoComp-cong (idIso (edge₂ t)) (
        (isoComp-unitʳ-at (g ◁ l) ∙
        (isoComp-cong (idIso (g ◁ l)) (isoComp-inverseˡ-at (edge₂ s)) ∙
          isoComp-assoc-at (g ◁ l) ((edge₂ s) ⁻¹) (edge₂ s))) ⁻¹)
```
