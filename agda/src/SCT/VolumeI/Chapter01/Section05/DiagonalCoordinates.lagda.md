# Reading a diagonal cone in its two coordinates

A matching into a product is read by its two projections. The displayed
normalizations retain the associators and product projection comparisons.
The two resulting isomorphisms have a common target, so their quotient
is the matching of an ordinary pullback cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as Pairing

module SCT.VolumeI.Chapter01.Section05.DiagonalCoordinates
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯
  using (transport-square; reflect-transport-square; post-square; decode-encode)
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
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

  left₁ : {T : CAT} (u : MAP T (C × D)) → NatIso (pr₁ ∘ (F ∘ u)) (f ∘ (pr₁ ∘ u))
  left₁ u = comp-assoc u pr₁ f ∙ project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u
  left₂ : {T : CAT} (u : MAP T (C × D)) → NatIso (pr₂ ∘ (F ∘ u)) (g ∘ (pr₂ ∘ u))
  left₂ u = comp-assoc u pr₂ g ∙ project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u
  right₁ : {T : CAT} (v : MAP T E) → NatIso (pr₁ ∘ (Δ ∘ v)) v
  right₁ v = comp-unitˡ v ∙ project-pair₁ (id E) (id E) v
  right₂ : {T : CAT} (v : MAP T E) → NatIso (pr₂ ∘ (Δ ∘ v)) v
  right₂ v = comp-unitˡ v ∙ project-pair₂ (id E) (id E) v

  edge₁ : {T : CAT} (t : Cone F Δ T) → NatIso (f ∘ (pr₁ ∘ Cone.left t)) (Cone.right t)
  edge₁ t = right₁ (Cone.right t) ∙ ((pr₁ ◁ Cone.match t) ∙ invIso (left₁ (Cone.left t)))
  edge₂ : {T : CAT} (t : Cone F Δ T) → NatIso (g ∘ (pr₂ ∘ Cone.left t)) (Cone.right t)
  edge₂ t = right₂ (Cone.right t) ∙ ((pr₂ ◁ Cone.match t) ∙ invIso (left₂ (Cone.left t)))

  from : {T : CAT} → Cone F Δ T → Cone f g T
  from t = record { left = pr₁ ∘ Cone.left t ; right = pr₂ ∘ Cone.left t
                  ; match = invIso (edge₂ t) ∙ edge₁ t }

```

The normalizations commute with comparisons of the legs. Consequently,
a cone comparison can be read in coordinates, and two compatible
coordinate comparisons reconstruct a full cone comparison.

```agda

  opaque
    left₁-natural : {T : CAT} {u u′ : MAP T (C × D)} (L : NatIso u u′)
      → Iso₂ (left₁ u′ ∙ (pr₁ ◁ (F ◁ L))) ((f ◁ (pr₁ ◁ L)) ∙ left₁ u)
    left₁-natural {u = u} {u′} L = paste-squares
      (project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u) (project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u′)
      (comp-assoc u pr₁ f) (comp-assoc u′ pr₁ f)
      (pr₁ ◁ (F ◁ L)) ((f ∘ pr₁) ◁ L) (f ◁ (pr₁ ◁ L))
      (substitution-square-projection pr₁ F (f ∘ pr₁) (pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) L)
      (postWhisker-comp-at L pr₁ f)

    left₂-natural : {T : CAT} {u u′ : MAP T (C × D)} (L : NatIso u u′)
      → Iso₂ (left₂ u′ ∙ (pr₂ ◁ (F ◁ L))) ((g ◁ (pr₂ ◁ L)) ∙ left₂ u)
    left₂-natural {u = u} {u′} L = paste-squares
      (project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u) (project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u′)
      (comp-assoc u pr₂ g) (comp-assoc u′ pr₂ g)
      (pr₂ ◁ (F ◁ L)) ((g ∘ pr₂) ◁ L) (g ◁ (pr₂ ◁ L))
      (substitution-square-projection pr₂ F (g ∘ pr₂) (pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) L)
      (postWhisker-comp-at L pr₂ g)

    right₁-natural : {T : CAT} {v v′ : MAP T E} (R : NatIso v v′)
      → Iso₂ (right₁ v′ ∙ (pr₁ ◁ (Δ ◁ R))) (R ∙ right₁ v)
    right₁-natural {v = v} {v′} R = paste-squares
      (project-pair₁ (id E) (id E) v) (project-pair₁ (id E) (id E) v′)
      (comp-unitˡ v) (comp-unitˡ v′) (pr₁ ◁ (Δ ◁ R)) (id E ◁ R) R
      (substitution-square-projection pr₁ Δ (id E) (pair-β₁ (id E) (id E)) R)
      (postWhisker-id-at R)

    right₂-natural : {T : CAT} {v v′ : MAP T E} (R : NatIso v v′)
      → Iso₂ (right₂ v′ ∙ (pr₂ ◁ (Δ ◁ R))) (R ∙ right₂ v)
    right₂-natural {v = v} {v′} R = paste-squares
      (project-pair₂ (id E) (id E) v) (project-pair₂ (id E) (id E) v′)
      (comp-unitˡ v) (comp-unitˡ v′) (pr₂ ◁ (Δ ◁ R)) (id E ◁ R) R
      (substitution-square-projection pr₂ Δ (id E) (pair-β₂ (id E) (id E)) R)
      (postWhisker-id-at R)

  opaque
    coordinate₁ : {T : CAT} {s t : Cone F Δ T} (Φ : ConeIso s t)
      → Iso₂ (edge₁ t ∙ (f ◁ (pr₁ ◁ ConeIso.leftIso Φ))) (ConeIso.rightIso Φ ∙ edge₁ s)
    coordinate₁ {s = s} {t} Φ = transport-square
      (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
      (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
      (pr₁ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₁ ◁ (Δ ◁ ConeIso.rightIso Φ))
      (f ◁ (pr₁ ◁ ConeIso.leftIso Φ)) (ConeIso.rightIso Φ)
      (left₁-natural (ConeIso.leftIso Φ)) (right₁-natural (ConeIso.rightIso Φ))
      (post-square pr₁ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (Δ ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

    coordinate₂ : {T : CAT} {s t : Cone F Δ T} (Φ : ConeIso s t)
      → Iso₂ (edge₂ t ∙ (g ◁ (pr₂ ◁ ConeIso.leftIso Φ))) (ConeIso.rightIso Φ ∙ edge₂ s)
    coordinate₂ {s = s} {t} Φ = transport-square
      (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
      (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
      (pr₂ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₂ ◁ (Δ ◁ ConeIso.rightIso Φ))
      (g ◁ (pr₂ ◁ ConeIso.leftIso Φ)) (ConeIso.rightIso Φ)
      (left₂-natural (ConeIso.leftIso Φ)) (right₂-natural (ConeIso.rightIso Φ))
      (post-square pr₂ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (Δ ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

  cone-from-coordinates : {T : CAT} (s t : Cone F Δ T)
    (L : NatIso (Cone.left s) (Cone.left t)) (R : NatIso (Cone.right s) (Cone.right t))
    → Iso₂ (edge₁ t ∙ (f ◁ (pr₁ ◁ L))) (R ∙ edge₁ s)
    → Iso₂ (edge₂ t ∙ (g ◁ (pr₂ ◁ L))) (R ∙ edge₂ s)
    → ConeIso s t
  cone-from-coordinates s t L R e₁ e₂ = record
    { leftIso = L ; rightIso = R
    ; compatible = pair-iso-extensionality
      (invIso (postWhisker-isoComp-at pr₁ (Δ ◁ R) (Cone.match s)) ∙
      (reflect-transport-square
        (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
        (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t) (pr₁ ◁ (F ◁ L)) (pr₁ ◁ (Δ ◁ R))
        (f ◁ (pr₁ ◁ L)) R (left₁-natural L) (right₁-natural R) e₁ ∙
        postWhisker-isoComp-at pr₁ (Cone.match t) (F ◁ L)))
      (invIso (postWhisker-isoComp-at pr₂ (Δ ◁ R) (Cone.match s)) ∙
      (reflect-transport-square
        (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
        (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t) (pr₂ ◁ (F ◁ L)) (pr₂ ◁ (Δ ◁ R))
        (g ◁ (pr₂ ◁ L)) R (left₂-natural L) (right₂-natural R) e₂ ∙
        postWhisker-isoComp-at pr₂ (Cone.match t) (F ◁ L))) }

  from-iso : {T : CAT} {s t : Cone F Δ T} → ConeIso s t → ConeIso (from s) (from t)
  from-iso {s = s} {t} Φ = record
    { leftIso = pr₁ ◁ ConeIso.leftIso Φ ; rightIso = pr₂ ◁ ConeIso.leftIso Φ
    ; compatible = isoComp-assoc-at (g ◁ (pr₂ ◁ ConeIso.leftIso Φ)) (invIso (edge₂ s)) (edge₁ s) ∙
      (isoComp-cong (move-square (edge₂ t) (g ◁ (pr₂ ◁ ConeIso.leftIso Φ)) (ConeIso.rightIso Φ) (edge₂ s) (coordinate₂ Φ)) (idIso (edge₁ s)) ∙
      (invIso (isoComp-assoc-at (invIso (edge₂ t)) (ConeIso.rightIso Φ) (edge₁ s)) ∙
      (isoComp-cong (idIso (invIso (edge₂ t))) (coordinate₁ Φ) ∙
        isoComp-assoc-at (invIso (edge₂ t)) (edge₁ t) (f ◁ (pr₁ ◁ ConeIso.leftIso Φ))))) }

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
    L : NatIso (Cone.left s) (Cone.left t)
    L = pair-iso l r
    R : NatIso (Cone.right s) (Cone.right t)
    R = edge₂ t ∙ ((g ◁ r) ∙ invIso (edge₂ s))
    first : Iso₂ (edge₁ t ∙ (f ◁ l)) (R ∙ edge₁ s)
    first = invIso (isoComp-assoc-at (edge₂ t) ((g ◁ r) ∙ invIso (edge₂ s)) (edge₁ s)) ∙
      (isoComp-cong (idIso (edge₂ t)) (invIso (isoComp-assoc-at (g ◁ r) (invIso (edge₂ s)) (edge₁ s))) ∙
      (isoComp-cong (idIso (edge₂ t)) (ConeIso.compatible Φ) ∙
      (isoComp-assoc-at (edge₂ t) (invIso (edge₂ t) ∙ edge₁ t) (f ◁ l) ∙
        isoComp-cong (invIso (cancel-inverse (edge₂ t) (edge₁ t))) (idIso (f ◁ l)))))
    second : Iso₂ (edge₂ t ∙ (g ◁ r)) (R ∙ edge₂ s)
    second = invIso (isoComp-assoc-at (edge₂ t) ((g ◁ r) ∙ invIso (edge₂ s)) (edge₂ s)) ∙
      isoComp-cong (idIso (edge₂ t)) (invIso
        (isoComp-unitʳ-at (g ◁ r) ∙
        (isoComp-cong (idIso (g ◁ r)) (isoComp-inverseˡ-at (edge₂ s)) ∙
          isoComp-assoc-at (g ◁ r) (invIso (edge₂ s)) (edge₂ s))))

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
    first = invIso (right₁ v) ∙ (α ∙ left₁ u)
    second = invIso (right₂ v) ∙ (β ∙ left₂ u)
    value : Cone F Δ T
    value = record { left = u ; right = v ; match = pair-iso first second }

    opaque
      edge₁-comparison : Iso₂ (edge₁ value) α
      edge₁-comparison = decode-encode (left₁ u) (right₁ v) α ∙
        isoComp-cong (idIso (right₁ v))
          (isoComp-cong (pair-iso-β₁ first second) (idIso (invIso (left₁ u))))

      edge₂-comparison : Iso₂ (edge₂ value) β
      edge₂-comparison = decode-encode (left₂ u) (right₂ v) β ∙
        isoComp-cong (idIso (right₂ v))
          (isoComp-cong (pair-iso-β₂ first second) (idIso (invIso (left₂ u))))

    recover : ConeIso (from value) s
    recover = record
      { leftIso = pair-β₁ p q ; rightIso = pair-β₂ p q
      ; compatible = isoComp-cong edge₂-comparison (idIso (invIso (edge₂ value) ∙ edge₁ value)) ∙
          (invIso (cancel-inverse (edge₂ value) (edge₁ value)) ∙ invIso edge₁-comparison) }
```
