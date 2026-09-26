# Coordinates of a cone to paired functors

Projecting the matching gives two coordinate equations. Conversely, those
two equations reconstruct the full cone comparison with its specified legs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing

module SCT.VolumeI.Chapter01.Section06.Coordinates.PairedConeCoordinates
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (transport-square; reflect-transport-square; post-square; decode-encode)
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection; move-square; cancel-right)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; postWhisker-id-at)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-pre-triangle₁; pair-pre-triangle₂)

open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
  using (restricted-normalization; coordinate-pre)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)

normalization-restrict : {R T A B C : CAT} (π : MAP B C) (F : MAP A B) (f : MAP A C)
  (β : (π ∘ F) =₁ f) (u : MAP T A) (r : MAP R T) →
  restricted-normalization π F u (transport-pre π F β u) r =₂
    ((comp-assoc r u f) ⁻¹ ∙ transport-pre π F β (u ∘ r))
normalization-restrict π F f β u r =
  (move-square (comp-assoc r u f)
    ((transport-pre π F β u ▷ r) ∙ (comp-assoc r (F ∘ u) π) ⁻¹)
    (transport-pre π F β (u ∘ r)) (π ◁ comp-assoc r u F)
    (transport-pre-assoc π F f β u r ∙
      (isoComp-assoc-at (comp-assoc r u f) (transport-pre π F β u ▷ r)
        ((comp-assoc r (F ∘ u) π) ⁻¹)) ⁻¹)) ⁻¹

module Coordinates {A B C D : CAT} (f₀ : MAP A C) (f₁ : MAP A D)
  (g₀ : MAP B C) (g₁ : MAP B D) where
  F = pair f₀ f₁
  G = pair g₀ g₁

  left₁ : {T : CAT} (u : MAP T A) → (pr₁ ∘ (F ∘ u)) =₁ (f₀ ∘ u)
  left₁ u = project-pair₁ f₀ f₁ u
  right₁ : {T : CAT} (v : MAP T B) → (pr₁ ∘ (G ∘ v)) =₁ (g₀ ∘ v)
  right₁ v = project-pair₁ g₀ g₁ v

  edge₁ : {T : CAT} (t : Cone F G T) → (f₀ ∘ Cone.left t) =₁ (g₀ ∘ Cone.right t)
  edge₁ t = right₁ (Cone.right t) ∙ ((pr₁ ◁ Cone.match t) ∙ (left₁ (Cone.left t)) ⁻¹)

  left₁-natural : {T : CAT} {u u′ : MAP T A} (L : u =₁ u′) →
    (left₁ u′ ∙ (pr₁ ◁ (F ◁ L))) =₂ ((f₀ ◁ L) ∙ left₁ u)
  left₁-natural L = substitution-square-projection pr₁ F f₀ (pair-β₁ f₀ f₁) L
  right₁-natural : {T : CAT} {v v′ : MAP T B} (R : v =₁ v′) →
    (right₁ v′ ∙ (pr₁ ◁ (G ◁ R))) =₂ ((g₀ ◁ R) ∙ right₁ v)
  right₁-natural R = substitution-square-projection pr₁ G g₀ (pair-β₁ g₀ g₁) R

  coordinate₁ : {T : CAT} {s t : Cone F G T} (Φ : ConeIso s t) →
    (edge₁ t ∙ (f₀ ◁ ConeIso.leftIso Φ)) =₂ ((g₀ ◁ ConeIso.rightIso Φ) ∙ edge₁ s)
  coordinate₁ {s = s} {t} Φ = transport-square
    (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
    (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
    (pr₁ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₁ ◁ (G ◁ ConeIso.rightIso Φ))
    (f₀ ◁ ConeIso.leftIso Φ) (g₀ ◁ ConeIso.rightIso Φ)
    (left₁-natural (ConeIso.leftIso Φ)) (right₁-natural (ConeIso.rightIso Φ))
    (post-square pr₁ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (G ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

  left₂ : {T : CAT} (u : MAP T A) → (pr₂ ∘ (F ∘ u)) =₁ (f₁ ∘ u)
  left₂ u = project-pair₂ f₀ f₁ u
  right₂ : {T : CAT} (v : MAP T B) → (pr₂ ∘ (G ∘ v)) =₁ (g₁ ∘ v)
  right₂ v = project-pair₂ g₀ g₁ v

  edge₂ : {T : CAT} (t : Cone F G T) → (f₁ ∘ Cone.left t) =₁ (g₁ ∘ Cone.right t)
  edge₂ t = right₂ (Cone.right t) ∙ ((pr₂ ◁ Cone.match t) ∙ (left₂ (Cone.left t)) ⁻¹)

  left₂-natural : {T : CAT} {u u′ : MAP T A} (L : u =₁ u′) →
    (left₂ u′ ∙ (pr₂ ◁ (F ◁ L))) =₂ ((f₁ ◁ L) ∙ left₂ u)
  left₂-natural L = substitution-square-projection pr₂ F f₁ (pair-β₂ f₀ f₁) L
  right₂-natural : {T : CAT} {v v′ : MAP T B} (R : v =₁ v′) →
    (right₂ v′ ∙ (pr₂ ◁ (G ◁ R))) =₂ ((g₁ ◁ R) ∙ right₂ v)
  right₂-natural R = substitution-square-projection pr₂ G g₁ (pair-β₂ g₀ g₁) R

  coordinate₂ : {T : CAT} {s t : Cone F G T} (Φ : ConeIso s t) →
    (edge₂ t ∙ (f₁ ◁ ConeIso.leftIso Φ)) =₂ ((g₁ ◁ ConeIso.rightIso Φ) ∙ edge₂ s)
  coordinate₂ {s = s} {t} Φ = transport-square
    (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
    (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
    (pr₂ ◁ (F ◁ ConeIso.leftIso Φ)) (pr₂ ◁ (G ◁ ConeIso.rightIso Φ))
    (f₁ ◁ ConeIso.leftIso Φ) (g₁ ◁ ConeIso.rightIso Φ)
    (left₂-natural (ConeIso.leftIso Φ)) (right₂-natural (ConeIso.rightIso Φ))
    (post-square pr₂ (Cone.match s) (Cone.match t) (F ◁ ConeIso.leftIso Φ) (G ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ))

  cone-from-coordinates : {T : CAT} (s t : Cone F G T)
    (L : Cone.left s =₁ Cone.left t) (R : Cone.right s =₁ Cone.right t) →
    (edge₁ t ∙ (f₀ ◁ L)) =₂ ((g₀ ◁ R) ∙ edge₁ s) →
    (edge₂ t ∙ (f₁ ◁ L)) =₂ ((g₁ ◁ R) ∙ edge₂ s) → ConeIso s t
  cone-from-coordinates s t L R e₁ e₂ = record
    { leftIso = L ; rightIso = R
    ; compatible = pair-iso-extensionality
      ((postWhisker-isoComp-at pr₁ (G ◁ R) (Cone.match s)) ⁻¹ ∙
        (reflect-transport-square
          (left₁ (Cone.left s)) (left₁ (Cone.left t)) (right₁ (Cone.right s)) (right₁ (Cone.right t))
          (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t) (pr₁ ◁ (F ◁ L)) (pr₁ ◁ (G ◁ R))
          (f₀ ◁ L) (g₀ ◁ R) (left₁-natural L) (right₁-natural R) e₁ ∙
          postWhisker-isoComp-at pr₁ (Cone.match t) (F ◁ L)))
      ((postWhisker-isoComp-at pr₂ (G ◁ R) (Cone.match s)) ⁻¹ ∙
        (reflect-transport-square
          (left₂ (Cone.left s)) (left₂ (Cone.left t)) (right₂ (Cone.right s)) (right₂ (Cone.right t))
          (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t) (pr₂ ◁ (F ◁ L)) (pr₂ ◁ (G ◁ R))
          (f₁ ◁ L) (g₁ ◁ R) (left₂-natural L) (right₂-natural R) e₂ ∙
          postWhisker-isoComp-at pr₂ (Cone.match t) (F ◁ L)))
      }

  edge₁-restrict : {R T : CAT} (r : MAP R T) (t : Cone F G T) →
    edge₁ (conePre r t) =₂
      (comp-assoc r (Cone.right t) g₀ ∙
        ((edge₁ t ▷ r) ∙ (comp-assoc r (Cone.left t) f₀) ⁻¹))
  edge₁-restrict r t = (cancel-inverse AR (edge₁ (conePre r t)) ∙
    (isoComp-cong (idIso AR) (isoComp-assoc-at (AR ⁻¹) rn middle) ∙
      isoComp-cong (idIso AR) calculation ⁻¹)) ⁻¹
    where
    AL = comp-assoc r (Cone.left t) f₀
    AR = comp-assoc r (Cone.right t) g₀
    ln = left₁ (Cone.left t ∘ r)
    rn = right₁ (Cone.right t ∘ r)
    middle = (pr₁ ◁ Cone.match (conePre r t)) ∙ ln ⁻¹
    calculation = coordinate-pre pr₁ t r (left₁ (Cone.left t)) (right₁ (Cone.right t))
      ln (AR ⁻¹ ∙ rn) (AL ⁻¹)
      (normalization-restrict pr₁ F f₀ (pair-β₁ f₀ f₁) (Cone.left t) r)
      (normalization-restrict pr₁ G g₀ (pair-β₁ g₀ g₁) (Cone.right t) r)

  edge₂-restrict : {R T : CAT} (r : MAP R T) (t : Cone F G T) →
    edge₂ (conePre r t) =₂
      (comp-assoc r (Cone.right t) g₁ ∙
        ((edge₂ t ▷ r) ∙ (comp-assoc r (Cone.left t) f₁) ⁻¹))
  edge₂-restrict r t = (cancel-inverse AR (edge₂ (conePre r t)) ∙
    (isoComp-cong (idIso AR) (isoComp-assoc-at (AR ⁻¹) rn middle) ∙
      isoComp-cong (idIso AR) calculation ⁻¹)) ⁻¹
    where
    AL = comp-assoc r (Cone.left t) f₁
    AR = comp-assoc r (Cone.right t) g₁
    ln = left₂ (Cone.left t ∘ r)
    rn = right₂ (Cone.right t ∘ r)
    middle = (pr₂ ◁ Cone.match (conePre r t)) ∙ ln ⁻¹
    calculation = coordinate-pre pr₂ t r (left₂ (Cone.left t)) (right₂ (Cone.right t))
      ln (AR ⁻¹ ∙ rn) (AL ⁻¹)
      (normalization-restrict pr₂ F f₁ (pair-β₂ f₀ f₁) (Cone.left t) r)
      (normalization-restrict pr₂ G g₁ (pair-β₂ g₀ g₁) (Cone.right t) r)

  encode : {T : CAT} (u : MAP T A) (v : MAP T B) →
    (f₀ ∘ u) =₁ (g₀ ∘ v) → (f₁ ∘ u) =₁ (g₁ ∘ v) → Cone F G T
  encode u v α β = record { left = u ; right = v
    ; match = (pair-pre g₀ g₁ v) ⁻¹ ∙ (pair-cong α β ∙ pair-pre f₀ f₁ u) }

  encode-edge₁ : {T : CAT} (u : MAP T A) (v : MAP T B)
    (α : (f₀ ∘ u) =₁ (g₀ ∘ v)) (β : (f₁ ∘ u) =₁ (g₁ ∘ v)) →
    edge₁ (encode u v α β) =₂ α
  encode-edge₁ u v α β = cancel-right (left₁ u) α ∙
    (isoComp-cong triangle (idIso ((left₁ u) ⁻¹)) ∙
      (isoComp-assoc-at (right₁ v) (pr₁ ◁ δ) ((left₁ u) ⁻¹)) ⁻¹)
    where
    K = pair-cong α β ∙ pair-pre f₀ f₁ u
    R = pair-pre g₀ g₁ v
    δ = R ⁻¹ ∙ K
    projected = (postWhisker pr₁ ◁ cancel-inverse R K) ∙
      (postWhisker-isoComp-at pr₁ R δ) ⁻¹
    triangle : (right₁ v ∙ (pr₁ ◁ δ)) =₂ (α ∙ left₁ u)
    triangle = pair-pre-cong-triangle₁ f₀ f₁ u α β ∙
      (isoComp-cong (idIso (pair-β₁ (g₀ ∘ v) (g₁ ∘ v))) projected ∙
        (isoComp-assoc-at (pair-β₁ (g₀ ∘ v) (g₁ ∘ v)) (pr₁ ◁ R) (pr₁ ◁ δ) ∙
          isoComp-cong ((pair-pre-triangle₁ g₀ g₁ v) ⁻¹) (idIso (pr₁ ◁ δ))))

  encode-edge₂ : {T : CAT} (u : MAP T A) (v : MAP T B)
    (α : (f₀ ∘ u) =₁ (g₀ ∘ v)) (β : (f₁ ∘ u) =₁ (g₁ ∘ v)) →
    edge₂ (encode u v α β) =₂ β
  encode-edge₂ u v α β = cancel-right (left₂ u) β ∙
    (isoComp-cong triangle (idIso ((left₂ u) ⁻¹)) ∙
      (isoComp-assoc-at (right₂ v) (pr₂ ◁ δ) ((left₂ u) ⁻¹)) ⁻¹)
    where
    K = pair-cong α β ∙ pair-pre f₀ f₁ u
    R = pair-pre g₀ g₁ v
    δ = R ⁻¹ ∙ K
    projected = (postWhisker pr₂ ◁ cancel-inverse R K) ∙
      (postWhisker-isoComp-at pr₂ R δ) ⁻¹
    triangle : (right₂ v ∙ (pr₂ ◁ δ)) =₂ (β ∙ left₂ u)
    triangle = pair-pre-cong-triangle₂ f₀ f₁ u α β ∙
      (isoComp-cong (idIso (pair-β₂ (g₀ ∘ v) (g₁ ∘ v))) projected ∙
        (isoComp-assoc-at (pair-β₂ (g₀ ∘ v) (g₁ ∘ v)) (pr₂ ◁ R) (pr₂ ◁ δ) ∙
          isoComp-cong ((pair-pre-triangle₂ g₀ g₁ v) ⁻¹) (idIso (pr₂ ◁ δ))))
```
