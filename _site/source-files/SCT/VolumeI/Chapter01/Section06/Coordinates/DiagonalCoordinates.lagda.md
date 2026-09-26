# Reading a diagonal cone in its two coordinates

A matching into a product is read by its two projections. The displayed
normalizations retain the associators and product projection comparisons.
The two resulting isomorphisms have a common target, so their quotient
is the matching of an ordinary pullback cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing

module SCT.VolumeI.Chapter01.Section06.Coordinates.DiagonalCoordinates
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
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

module Coordinates {C D E : CAT} (f : MAP C E) (g : MAP D E) where

  F : MAP (C × D) (E × E)
  F = productMap f g
  Δ : MAP E (E × E)
  Δ = pair (id E) (id E)

  left₁ : {T : CAT} (u : MAP T (C × D)) → (pr₁ ∘ (F ∘ u)) =₁ (f ∘ (pr₁ ∘ u))
  left₁ u = comp-assoc u pr₁ f ∙ project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u
  left₂ : {T : CAT} (u : MAP T (C × D)) → (pr₂ ∘ (F ∘ u)) =₁ (g ∘ (pr₂ ∘ u))
  left₂ u = comp-assoc u pr₂ g ∙ project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u
  right₁ : {T : CAT} (v : MAP T E) → (pr₁ ∘ (Δ ∘ v)) =₁ v
  right₁ v = comp-unitˡ v ∙ project-pair₁ (id E) (id E) v
  right₂ : {T : CAT} (v : MAP T E) → (pr₂ ∘ (Δ ∘ v)) =₁ v
  right₂ v = comp-unitˡ v ∙ project-pair₂ (id E) (id E) v

  edge₁ : {T : CAT} (t : Cone F Δ T) → (f ∘ (pr₁ ∘ Cone.left t)) =₁ (Cone.right t)
  edge₁ t = right₁ (Cone.right t) ∙ ((pr₁ ◁ Cone.match t) ∙ (left₁ (Cone.left t)) ⁻¹)
  edge₂ : {T : CAT} (t : Cone F Δ T) → (g ∘ (pr₂ ∘ Cone.left t)) =₁ (Cone.right t)
  edge₂ t = right₂ (Cone.right t) ∙ ((pr₂ ◁ Cone.match t) ∙ (left₂ (Cone.left t)) ⁻¹)

  from : {T : CAT} → Cone F Δ T → Cone f g T
  from t = record { left = pr₁ ∘ Cone.left t ; right = pr₂ ∘ Cone.left t
                  ; match = (edge₂ t) ⁻¹ ∙ edge₁ t }

```

The normalizations commute with comparisons of the legs. Consequently,
a cone comparison can be read in coordinates, and two compatible
coordinate comparisons reconstruct a full cone comparison.

```agda

  opaque
    left₁-natural : {T : CAT} {u u′ : MAP T (C × D)} (L : u =₁ u′)
      → (left₁ u′ ∙ (pr₁ ◁ (F ◁ L))) =₂ ((f ◁ (pr₁ ◁ L)) ∙ left₁ u)
    left₁-natural {u = u} {u′} L = paste-squares
      (project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u) (project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u′)
      (comp-assoc u pr₁ f) (comp-assoc u′ pr₁ f)
      (pr₁ ◁ (F ◁ L)) ((f ∘ pr₁) ◁ L) (f ◁ (pr₁ ◁ L))
      (substitution-square-projection pr₁ F (f ∘ pr₁) (pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) L)
      (postWhisker-comp-at L pr₁ f)

    left₂-natural : {T : CAT} {u u′ : MAP T (C × D)} (L : u =₁ u′)
      → (left₂ u′ ∙ (pr₂ ◁ (F ◁ L))) =₂ ((g ◁ (pr₂ ◁ L)) ∙ left₂ u)
    left₂-natural {u = u} {u′} L = paste-squares
      (project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u) (project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u′)
      (comp-assoc u pr₂ g) (comp-assoc u′ pr₂ g)
      (pr₂ ◁ (F ◁ L)) ((g ∘ pr₂) ◁ L) (g ◁ (pr₂ ◁ L))
      (substitution-square-projection pr₂ F (g ∘ pr₂) (pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) L)
      (postWhisker-comp-at L pr₂ g)

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
      → (edge₁ t ∙ (f ◁ (pr₁ ◁ ConeIso.leftIso Φ))) =₂ (ConeIso.rightIso Φ ∙ edge₁ s)
    coordinate₁ {s = s} {t} Φ = transport-square
      (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
      (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
      (pr₁ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₁ ◁ (Δ ◁ ConeIso.rightIso Φ))
      (f ◁ (pr₁ ◁ ConeIso.leftIso Φ)) (ConeIso.rightIso Φ)
      (left₁-natural (ConeIso.leftIso Φ)) (right₁-natural (ConeIso.rightIso Φ))
      (post-square pr₁ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (Δ ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

    coordinate₂ : {T : CAT} {s t : Cone F Δ T} (Φ : ConeIso s t)
      → (edge₂ t ∙ (g ◁ (pr₂ ◁ ConeIso.leftIso Φ))) =₂ (ConeIso.rightIso Φ ∙ edge₂ s)
    coordinate₂ {s = s} {t} Φ = transport-square
      (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
      (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
      (pr₂ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₂ ◁ (Δ ◁ ConeIso.rightIso Φ))
      (g ◁ (pr₂ ◁ ConeIso.leftIso Φ)) (ConeIso.rightIso Φ)
      (left₂-natural (ConeIso.leftIso Φ)) (right₂-natural (ConeIso.rightIso Φ))
      (post-square pr₂ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (Δ ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

  cone-from-coordinates : {T : CAT} (s t : Cone F Δ T)
    (L : (Cone.left s) =₁ (Cone.left t)) (R : (Cone.right s) =₁ (Cone.right t))
    → (edge₁ t ∙ (f ◁ (pr₁ ◁ L))) =₂ (R ∙ edge₁ s)
    → (edge₂ t ∙ (g ◁ (pr₂ ◁ L))) =₂ (R ∙ edge₂ s)
    → ConeIso s t
  cone-from-coordinates s t L R e₁ e₂ = record
    { leftIso = L ; rightIso = R
    ; compatible = pair-iso-extensionality
      ((postWhisker-isoComp-at pr₁ (Δ ◁ R) (Cone.match s)) ⁻¹ ∙
      (reflect-transport-square
        (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
        (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t) (pr₁ ◁ (F ◁ L)) (pr₁ ◁ (Δ ◁ R))
        (f ◁ (pr₁ ◁ L)) R (left₁-natural L) (right₁-natural R) e₁ ∙
        postWhisker-isoComp-at pr₁ (Cone.match t) (F ◁ L)))
      ((postWhisker-isoComp-at pr₂ (Δ ◁ R) (Cone.match s)) ⁻¹ ∙
      (reflect-transport-square
        (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
        (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t) (pr₂ ◁ (F ◁ L)) (pr₂ ◁ (Δ ◁ R))
        (g ◁ (pr₂ ◁ L)) R (left₂-natural L) (right₂-natural R) e₂ ∙
        postWhisker-isoComp-at pr₂ (Cone.match t) (F ◁ L))) }

  from-iso : {T : CAT} {s t : Cone F Δ T} → ConeIso s t → ConeIso (from s) (from t)
  from-iso {s = s} {t} Φ = record
    { leftIso = pr₁ ◁ ConeIso.leftIso Φ ; rightIso = pr₂ ◁ ConeIso.leftIso Φ
    ; compatible = isoComp-assoc-at (g ◁ (pr₂ ◁ ConeIso.leftIso Φ)) ((edge₂ s) ⁻¹) (edge₁ s) ∙
      (isoComp-cong (move-square (edge₂ t) (g ◁ (pr₂ ◁ ConeIso.leftIso Φ)) (ConeIso.rightIso Φ) (edge₂ s) (coordinate₂ Φ)) (idIso (edge₁ s)) ∙
      ((isoComp-assoc-at ((edge₂ t) ⁻¹) (ConeIso.rightIso Φ) (edge₁ s)) ⁻¹ ∙
      (isoComp-cong (idIso ((edge₂ t) ⁻¹)) (coordinate₁ Φ) ∙
        isoComp-assoc-at ((edge₂ t) ⁻¹) (edge₁ t) (f ◁ (pr₁ ◁ ConeIso.leftIso Φ))))) }

```

Recovery also reflects the existence of a cone comparison. Product lifting
gives its left leg; the second coordinate determines its right leg.
The first coordinate equation is precisely the recovered compatibility.

```agda
  from-reflect : {T : CAT} {s t : Cone F Δ T} → ConeIso (from s) (from t) → ConeIso s t
  from-reflect {s = s} {t} Φ = cone-from-coordinates s t L R
    (first ∙ isoComp-cong (idIso (edge₁ t)) (postWhisker f ◁ pair-iso-β₁ l r))
    (second ∙ isoComp-cong (idIso (edge₂ t)) (postWhisker g ◁ pair-iso-β₂ l r))
    where
    l = ConeIso.leftIso Φ
    r = ConeIso.rightIso Φ
    L : (Cone.left s) =₁ (Cone.left t)
    L = pair-iso l r
    R : (Cone.right s) =₁ (Cone.right t)
    R = edge₂ t ∙ ((g ◁ r) ∙ (edge₂ s) ⁻¹)
    first : (edge₁ t ∙ (f ◁ l)) =₂ (R ∙ edge₁ s)
    first = (isoComp-assoc-at (edge₂ t) ((g ◁ r) ∙ (edge₂ s) ⁻¹) (edge₁ s)) ⁻¹ ∙
      (isoComp-cong (idIso (edge₂ t)) ((isoComp-assoc-at (g ◁ r) ((edge₂ s) ⁻¹) (edge₁ s)) ⁻¹) ∙
      (isoComp-cong (idIso (edge₂ t)) (ConeIso.compatible Φ) ∙
      (isoComp-assoc-at (edge₂ t) ((edge₂ t) ⁻¹ ∙ edge₁ t) (f ◁ l) ∙
        isoComp-cong ((cancel-inverse (edge₂ t) (edge₁ t)) ⁻¹) (idIso (f ◁ l)))))
    second : (edge₂ t ∙ (g ◁ r)) =₂ (R ∙ edge₂ s)
    second = (isoComp-assoc-at (edge₂ t) ((g ◁ r) ∙ (edge₂ s) ⁻¹) (edge₂ s)) ⁻¹ ∙
      isoComp-cong (idIso (edge₂ t)) (
        (isoComp-unitʳ-at (g ◁ r) ∙
        (isoComp-cong (idIso (g ◁ r)) (isoComp-inverseˡ-at (edge₂ s)) ∙
          isoComp-assoc-at (g ◁ r) ((edge₂ s) ⁻¹) (edge₂ s))) ⁻¹)

```

For the direct square, prescribe the first matching coordinate using `τ`
and the second using the identity. The beta comparisons account for the
two product projections. Recovering this square gives the original cone
with those beta comparisons as its legs.

```agda
  module Direct {T : CAT} (s : Cone f g T) where
    p = Cone.left s
    q = Cone.right s
    τ = Cone.match s
    u = pair p q
    v = g ∘ q
    α = τ ∙ (f ◁ pair-β₁ p q)
    β = g ◁ pair-β₂ p q
    first = (right₁ v) ⁻¹ ∙ (α ∙ left₁ u)
    second = (right₂ v) ⁻¹ ∙ (β ∙ left₂ u)
    value : Cone F Δ T
    value = record { left = u ; right = v ; match = pair-iso first second }

    opaque
      edge₁-comparison : (edge₁ value) =₂ α
      edge₁-comparison = decode-encode (left₁ u) (right₁ v) α ∙
        isoComp-cong (idIso (right₁ v))
          (isoComp-cong (pair-iso-β₁ first second) (idIso ((left₁ u) ⁻¹)))

      edge₂-comparison : (edge₂ value) =₂ β
      edge₂-comparison = decode-encode (left₂ u) (right₂ v) β ∙
        isoComp-cong (idIso (right₂ v))
          (isoComp-cong (pair-iso-β₂ first second) (idIso ((left₂ u) ⁻¹)))

    recover : ConeIso (from value) s
    recover = record
      { leftIso = pair-β₁ p q ; rightIso = pair-β₂ p q
      ; compatible = isoComp-cong edge₂-comparison (idIso ((edge₂ value) ⁻¹ ∙ edge₁ value)) ∙
          ((cancel-inverse (edge₂ value) (edge₁ value)) ⁻¹ ∙ edge₁-comparison ⁻¹) }
```
