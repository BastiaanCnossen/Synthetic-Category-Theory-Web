# Images of fiber cones

A commuting square maps a fiber cone to a fiber cone. The target family
may have a specified identification with the image family. The normalized
matching retains both comparisons. The construction acts on whole cone
comparisons and commutes with restriction, including their matchings.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated

module SCT.VolumeI.Chapter01.Section06.Cospans.FiberImages
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse; coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.FramedEdgeCones as Edges
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.TriangleCones as Triangles
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection; move-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre-assoc)

module Along {C D E B Γ : CAT}
  (u : MAP C D) (family : MAP Γ D) (f : MAP C E)
  (w : MAP E B) (b : MAP D B) (e : MAP Γ B)
  (α : (b ∘ u) =₁ (w ∘ f)) (δ : (b ∘ family) =₁ e) where

  left-normal : {X : CAT} (p : MAP X C) → (b ∘ (u ∘ p)) =₁ (w ∘ (f ∘ p))
  left-normal p = comp-assoc p f w ∙ ((α ▷ p) ∙ (comp-assoc p u b) ⁻¹)
  right-normal : {X : CAT} (r : MAP X Γ) → (b ∘ (family ∘ r)) =₁ (e ∘ r)
  right-normal r = (δ ▷ r) ∙ (comp-assoc r family b) ⁻¹

  value : {X : CAT} → Cone u family X → Cone w e X
  value q = record { left = f ∘ Cone.left q ; right = Cone.right q
    ; match = right-normal (Cone.right q) ∙
        ((b ◁ Cone.match q) ∙ (left-normal (Cone.left q)) ⁻¹) }

  abstract
    left-natural : {X : CAT} {p p′ : MAP X C} (β : p =₁ p′) →
      (left-normal p′ ∙ (b ◁ (u ◁ β))) =₂ ((w ◁ (f ◁ β)) ∙ left-normal p)
    left-natural {p = p} {p′} β = paste-squares
      ((α ▷ p) ∙ (comp-assoc p u b) ⁻¹) ((α ▷ p′) ∙ (comp-assoc p′ u b) ⁻¹)
      (comp-assoc p f w) (comp-assoc p′ f w)
      (b ◁ (u ◁ β)) ((w ∘ f) ◁ β) (w ◁ (f ◁ β))
      (substitution-square-projection b u (w ∘ f) α β) (postWhisker-comp-at β f w)

    right-natural : {X : CAT} {r r′ : MAP X Γ} (β : r =₁ r′) →
      (right-normal r′ ∙ (b ◁ (family ◁ β))) =₂ ((e ◁ β) ∙ right-normal r)
    right-natural β = substitution-square-projection b family e δ β

  action : {X : CAT} {q q′ : Cone u family X} → ConeIso q q′ → ConeIso (value q) (value q′)
  action {q = q} {q′} Φ = record
    { leftIso = f ◁ ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
    ; compatible = transport-square
        (left-normal (Cone.left q)) (left-normal (Cone.left q′))
        (right-normal (Cone.right q)) (right-normal (Cone.right q′))
        (b ◁ Cone.match q) (b ◁ Cone.match q′)
        (b ◁ (u ◁ ConeIso.leftIso Φ)) (b ◁ (family ◁ ConeIso.rightIso Φ))
        (w ◁ (f ◁ ConeIso.leftIso Φ)) (e ◁ ConeIso.rightIso Φ)
        (left-natural (ConeIso.leftIso Φ)) (right-natural (ConeIso.rightIso Φ))
        (post-square b (Cone.match q) (Cone.match q′)
          (u ◁ ConeIso.leftIso Φ) (family ◁ ConeIso.rightIso Φ) (ConeIso.compatible Φ)) }

  abstract
    right-pre : {X Y : CAT} (r : MAP X Γ) (k : MAP Y X) →
      restricted-normalization b family r (right-normal r) k =₂
        ((comp-assoc k r e) ⁻¹ ∙ right-normal (r ∘ k))
    right-pre r k = (move-square (comp-assoc k r e)
      ((right-normal r ▷ k) ∙ (comp-assoc k (family ∘ r) b) ⁻¹)
      (right-normal (r ∘ k)) (b ◁ comp-assoc k r family)
      (transport-pre-assoc b family e δ r k ∙
        (isoComp-assoc-at (comp-assoc k r e) (right-normal r ▷ k)
          ((comp-assoc k (family ∘ r) b) ⁻¹)) ⁻¹)) ⁻¹

  restrict : {X Y : CAT} (k : MAP Y X) (q : Cone u family X) →
    ConeIso (value (conePre k q)) (conePre k (value q))
  restrict k q = record
    { leftIso = l ; rightIso = n
    ; compatible = normalize-cone-square AL AR σ σ′ (w ◁ l) (e ◁ n)
        (isoComp-assoc-at right-edge (right-normal (r ∘ k))
          ((b ◁ Cone.match (conePre k q)) ∙ (left-normal (p ∘ k)) ⁻¹) ∙ calculation ⁻¹) }
    where
    p = Cone.left q
    r = Cone.right q
    l = (comp-assoc k p f) ⁻¹
    n = idIso (r ∘ k)
    AL = comp-assoc k (f ∘ p) w
    AR = comp-assoc k r e
    L = AL ⁻¹ ∙ (w ◁ l)
    right-edge = AR ⁻¹ ∙ (e ◁ n)
    σ = Cone.match (value q) ▷ k
    σ′ = Cone.match (value (conePre k q))
    right-edge-normal : right-edge =₂ (AR ⁻¹)
    right-edge-normal = isoComp-unitʳ-at (AR ⁻¹) ∙
      isoComp-cong (idIso (AR ⁻¹)) (postWhisker-idIso e (r ∘ k))
    right-boundary = isoComp-cong (right-edge-normal ⁻¹) (idIso (right-normal (r ∘ k))) ∙ right-pre r k
    calculation = coordinate-pre b q k (left-normal p) (right-normal r)
      (left-normal (p ∘ k)) (right-edge ∙ right-normal (r ∘ k)) L
      (composite-normalization-pre b u f w α p k) right-boundary


  composite-value : {X : CAT} → Cone u family X → Cone (w ∘ f) e X
  composite-value q = record { left = Cone.left q ; right = Cone.right q
    ; match = Cone.match (value q) ∙ comp-assoc (Cone.left q) f w }

  private
    module Edge = Edges.At 𝒯 u b α e using (edge)
    module Triangle = Triangles.At 𝒯 b family e δ using (cone; normalized; restriction)

  factor-comparison : {X : CAT} (q : Cone u family X) →
    ConeIso (Edge.edge (composite-value q)) (Triangle.normalized (Cone.right q))
  factor-comparison q = record
    { leftIso = Cone.match q ; rightIso = idIso (Cone.right q)
    ; compatible = isoComp-cong ((postWhisker-idIso e (Cone.right q)) ⁻¹) (idIso M) ∙
        ((isoComp-unitˡ-at M) ⁻¹ ∙ calculation ⁻¹) }
    where
    p = Cone.left q
    r = Cone.right q
    χ = b ◁ Cone.match q
    A = comp-assoc p f w
    ψ = (α ▷ p) ∙ (comp-assoc p u b) ⁻¹
    L = left-normal p
    R = right-normal r
    σ = Cone.match (value q)
    M = Cone.match (Edge.edge (composite-value q))
    calculation : M =₂ (R ∙ χ)
    calculation = isoComp-cong (idIso R)
        (isoComp-unitʳ-at χ ∙ isoComp-cong (idIso χ) (isoComp-inverseˡ-at L)) ∙
      (isoComp-cong (idIso R) (isoComp-assoc-at χ (L ⁻¹) L) ∙
      (isoComp-assoc-at R (χ ∙ L ⁻¹) L ∙ isoComp-assoc-at σ A ψ))

  factor-restriction : {X : CAT} (q : Cone u family X) →
    ConeIso (Edge.edge (composite-value q)) (conePre (Cone.right q) Triangle.cone)
  factor-restriction q = coneIso-adjust
    (coneIso-compose (coneIso-inverse (Triangle.restriction (Cone.right q))) (factor-comparison q))
    (Cone.match q) ((comp-unitˡ (Cone.right q)) ⁻¹)
    (isoComp-unitˡ-at (Cone.match q) ∙
      isoComp-cong (inverse-identity (family ∘ Cone.right q)) (idIso (Cone.match q)))
    (isoComp-unitʳ-at ((comp-unitˡ (Cone.right q)) ⁻¹))
```
