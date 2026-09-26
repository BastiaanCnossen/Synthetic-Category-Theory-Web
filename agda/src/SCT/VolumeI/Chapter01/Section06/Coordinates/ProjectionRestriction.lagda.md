# Restricting normalized projection witnesses

These calculations compare a projection normalization restricted twice with
the normalization at the composite parameter. The associator calculation
uses the already proved pentagon; the identity case uses its unit consequence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits

module SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right; cancel-left; pre-square-projection)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc; pentagon-whiskered)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
  using (pentagon-left-corner; changeEndpoints-to-square; square-to-changeEndpoints)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯

restricted-normalization : {R T X Y Z : CAT} (π : MAP Y Z) (H : MAP X Y)
  (x : MAP T X) {y : MAP T Z} (n : (π ∘ (H ∘ x)) =₁ y) (r : MAP R T)
  → (π ∘ (H ∘ (x ∘ r))) =₁ (y ∘ r)
restricted-normalization π H x n r = transport-pre π (H ∘ x) n r ∙ (π ◁ comp-assoc r x H) ⁻¹

opaque
  normalization-pre : {R T X Y Z : CAT} (π : MAP Y Z) (H : MAP X Y) (k : MAP X Z)
    (β : (π ∘ H) =₁ k) (x : MAP T X) (r : MAP R T)
    {y : MAP T Z} (n : (k ∘ x) =₁ y)
    → (restricted-normalization π H x (n ∙ transport-pre π H β x) r) =₂
        (((n ▷ r) ∙ (comp-assoc r x k) ⁻¹) ∙ transport-pre π H β (x ∘ r))
  normalization-pre π H k β x r n =
    (isoComp-assoc-at (n ▷ r) (A ⁻¹) next) ⁻¹ ∙
    (isoComp-cong (idIso (n ▷ r)) core ∙
    (isoComp-assoc-at (n ▷ r) (old ∙ corner) (edge ⁻¹) ∙
    (isoComp-cong (isoComp-assoc-at (n ▷ r) old corner) (idIso (edge ⁻¹)) ∙
      isoComp-cong (isoComp-cong (preWhisker-isoComp-at n (transport-pre π H β x) r) (idIso corner)) (idIso (edge ⁻¹)))))
    where
    A : ((k ∘ x) ∘ r) =₁ (k ∘ (x ∘ r))
    A = comp-assoc r x k
    old : ((π ∘ (H ∘ x)) ∘ r) =₁ ((k ∘ x) ∘ r)
    old = transport-pre π H β x ▷ r
    next : (π ∘ (H ∘ (x ∘ r))) =₁ (k ∘ (x ∘ r))
    next = transport-pre π H β (x ∘ r)
    corner : (π ∘ ((H ∘ x) ∘ r)) =₁ ((π ∘ (H ∘ x)) ∘ r)
    corner = (comp-assoc r (H ∘ x) π) ⁻¹
    edge : (π ∘ ((H ∘ x) ∘ r)) =₁ (π ∘ (H ∘ (x ∘ r)))
    edge = π ◁ comp-assoc r x H
    core : ((old ∙ corner) ∙ edge ⁻¹) =₂ (A ⁻¹ ∙ next)
    core = (move-square A (old ∙ corner) next edge
      (transport-pre-assoc π H k β x r ∙ (isoComp-assoc-at A old corner) ⁻¹)) ⁻¹

  associator-corner : {R T X Y Z : CAT} (r : MAP R T) (u : MAP T X) (π : MAP X Y) (f : MAP Y Z)
    → ((comp-assoc u π f ▷ r) ∙ (comp-assoc r u (f ∘ π)) ⁻¹) =₂
        (((comp-assoc r (π ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u π) ⁻¹)) ∙ comp-assoc (u ∘ r) π f)
  associator-corner r u π f =
    isoComp-cong (isoComp-cong (idIso ((comp-assoc r (π ∘ u) f) ⁻¹)) ((post-inverse f (comp-assoc r u π)) ⁻¹))
      (idIso (comp-assoc (u ∘ r) π f)) ∙
    ((isoComp-assoc-at ((comp-assoc r (π ∘ u) f) ⁻¹) ((f ◁ comp-assoc r u π) ⁻¹) (comp-assoc (u ∘ r) π f)) ⁻¹ ∙
      (pentagon-left-corner (comp-assoc (u ∘ r) π f) (comp-assoc r u (f ∘ π))
        (f ◁ comp-assoc r u π) (comp-assoc r (π ∘ u) f) (comp-assoc u π f ▷ r)
        (pentagon-whiskered r u π f)) ⁻¹)

  unit-corner : {R T E : CAT} (r : MAP R T) (v : MAP T E)
    → ((comp-unitˡ v ▷ r) ∙ (comp-assoc r v (id E)) ⁻¹) =₂ (comp-unitˡ (v ∘ r))
  unit-corner r v = cancel-right (comp-assoc r v (id _)) (comp-unitˡ (v ∘ r)) ∙
    isoComp-cong ((left-unitor-comp r v) ⁻¹) (idIso ((comp-assoc r v (id _)) ⁻¹))

  composite-normalization-pre : {R T X Y Z W : CAT}
    (π : MAP Y Z) (H : MAP X Y) (q : MAP X W) (f : MAP W Z)
    (β : (π ∘ H) =₁ (f ∘ q)) (u : MAP T X) (r : MAP R T)
    → (restricted-normalization π H u (comp-assoc u q f ∙ transport-pre π H β u) r) =₂
      (((comp-assoc r (q ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u q) ⁻¹)) ∙
        (comp-assoc (u ∘ r) q f ∙ transport-pre π H β (u ∘ r)))
  composite-normalization-pre π H q f β u r =
    isoComp-assoc-at ((comp-assoc r (q ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u q) ⁻¹))
      (comp-assoc (u ∘ r) q f) (transport-pre π H β (u ∘ r)) ∙
    (isoComp-cong (associator-corner r u q f) (idIso (transport-pre π H β (u ∘ r))) ∙
      normalization-pre π H (f ∘ q) β u r (comp-assoc u q f))

  identity-normalization-pre : {R T Y Z : CAT}
    (π : MAP Y Z) (H : MAP Z Y) (β : (π ∘ H) =₁ (id Z)) (v : MAP T Z) (r : MAP R T)
    → (restricted-normalization π H v (comp-unitˡ v ∙ transport-pre π H β v) r) =₂
        (comp-unitˡ (v ∘ r) ∙ transport-pre π H β (v ∘ r))
  identity-normalization-pre π H β v r =
    isoComp-cong (unit-corner r v) (idIso (transport-pre π H β (v ∘ r))) ∙
      normalization-pre π H (id _) β v r (comp-unitˡ v)

  project-transport : {X Y Z : CAT} (π : MAP Y Z) {u u′ v v′ : MAP X Y}
    (L : u =₁ u′) (R : v =₁ v′) (σ : u =₁ v)
    → (π ◁ (R ∙ (σ ∙ L ⁻¹))) =₂ ((π ◁ R) ∙ ((π ◁ σ) ∙ (π ◁ L) ⁻¹))
  project-transport π L R σ = isoComp-cong (idIso (π ◁ R))
      (isoComp-cong (idIso (π ◁ σ)) (post-inverse π L) ∙ postWhisker-isoComp-at π σ (L ⁻¹)) ∙
    postWhisker-isoComp-at π R (σ ∙ L ⁻¹)

  extend-square : {X Y : CAT} {u u′ v v′ x y : MAP X Y}
    (L : u =₁ u′) (R : v =₁ v′) (σ : u =₁ v)
    (l : u =₁ x) (r : v =₁ y) (δ : x =₁ y)
    → (r ∙ σ) =₂ (δ ∙ l)
    → ((r ∙ R ⁻¹) ∙ (R ∙ (σ ∙ L ⁻¹))) =₂ (δ ∙ (l ∙ L ⁻¹))
  extend-square L R σ l r δ square = isoComp-assoc-at δ l (L ⁻¹) ∙
    (isoComp-cong square (idIso (L ⁻¹)) ∙
    ((isoComp-assoc-at r σ (L ⁻¹)) ⁻¹ ∙
    (isoComp-cong (idIso r) (cancel-left R (σ ∙ L ⁻¹)) ∙
      isoComp-assoc-at r (R ⁻¹) (R ∙ (σ ∙ L ⁻¹)))))

  coordinate-pre : {C D E Z S T : CAT} {F : MAP C E} {G : MAP D E}
    (π : MAP E Z) (t : Cone F G T) (r : MAP S T)
    {x y : MAP T Z} (l : (π ∘ (F ∘ Cone.left t)) =₁ x)
    (q : (π ∘ (G ∘ Cone.right t)) =₁ y)
    {x′ : MAP S Z} (l′ : (π ∘ (F ∘ (Cone.left t ∘ r))) =₁ x′)
    (q′ : (π ∘ (G ∘ (Cone.right t ∘ r))) =₁ (y ∘ r))
    (D′ : x′ =₁ (x ∘ r))
    → (restricted-normalization π F (Cone.left t) l r) =₂ (D′ ∙ l′)
    → (restricted-normalization π G (Cone.right t) q r) =₂ q′
    → (q′ ∙ ((π ◁ Cone.match (conePre r t)) ∙ l′ ⁻¹)) =₂
        (((q ∙ ((π ◁ Cone.match t) ∙ l ⁻¹)) ▷ r) ∙ D′)
  coordinate-pre {F = F} {G} π t r {x} {y} l q l′ q′ D′ left right =
    square-to-changeEndpoints l′ q′ (π ◁ Cone.match (conePre r t)) (δ ∙ D′)
      ((isoComp-assoc-at δ D′ l′) ⁻¹ ∙
      (isoComp-cong (idIso δ) left ∙
      (extend-square (π ◁ L) (π ◁ R) (π ◁ (Cone.match t ▷ r))
        (transport-pre π (F ∘ Cone.left t) l r) (transport-pre π (G ∘ Cone.right t) q r) δ
        (pre-square-projection π (Cone.match t) edge l q r
          (changeEndpoints-to-square l q (π ◁ Cone.match t) edge (idIso edge))) ∙
      (isoComp-cong (idIso (restricted-normalization π G (Cone.right t) q r)) (project-transport π L R (Cone.match t ▷ r)) ∙
        isoComp-cong (right ⁻¹) (idIso (π ◁ Cone.match (conePre r t)))))))
    where
    edge : x =₁ y
    edge = q ∙ ((π ◁ Cone.match t) ∙ l ⁻¹)
    δ : (x ∘ r) =₁ (y ∘ r)
    δ = edge ▷ r
    L : ((F ∘ Cone.left t) ∘ r) =₁ (F ∘ (Cone.left t ∘ r))
    L = comp-assoc r (Cone.left t) F
    R : ((G ∘ Cone.right t) ∘ r) =₁ (G ∘ (Cone.right t ∘ r))
    R = comp-assoc r (Cone.right t) G
```
