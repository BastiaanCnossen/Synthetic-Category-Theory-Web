# Restricting normalized projection witnesses

These calculations compare a projection normalization restricted twice with
the normalization at the composite parameter. The associator calculation
uses the already proved pentagon; the identity case uses its unit consequence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductUnits

module SCT.VolumeI.Chapter01.Section05.ProjectionRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right; cancel-left; pre-square-projection)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc; pentagon-whiskered)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
  using (pentagon-left-corner; changeEndpoints-to-square; square-to-changeEndpoints)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯

restricted-normalization : {R T X Y Z : CAT} (π : MAP Y Z) (H : MAP X Y)
  (x : MAP T X) {y : MAP T Z} (n : =₁ (π ∘ (H ∘ x)) y) (r : MAP R T)
  → =₁ (π ∘ (H ∘ (x ∘ r))) (y ∘ r)
restricted-normalization π H x n r = transport-pre π (H ∘ x) n r ∙ invIso (π ◁ comp-assoc r x H)

opaque
  normalization-pre : {R T X Y Z : CAT} (π : MAP Y Z) (H : MAP X Y) (k : MAP X Z)
    (β : =₁ (π ∘ H) k) (x : MAP T X) (r : MAP R T)
    {y : MAP T Z} (n : =₁ (k ∘ x) y)
    → =₂ (restricted-normalization π H x (n ∙ transport-pre π H β x) r)
        (((n ▷ r) ∙ invIso (comp-assoc r x k)) ∙ transport-pre π H β (x ∘ r))
  normalization-pre π H k β x r n =
    invIso (isoComp-assoc-at (n ▷ r) (invIso A) next) ∙
    (isoComp-cong (idIso (n ▷ r)) core ∙
    (isoComp-assoc-at (n ▷ r) (old ∙ corner) (invIso edge) ∙
    (isoComp-cong (isoComp-assoc-at (n ▷ r) old corner) (idIso (invIso edge)) ∙
      isoComp-cong (isoComp-cong (preWhisker-isoComp-at n (transport-pre π H β x) r) (idIso corner)) (idIso (invIso edge)))))
    where
    A : =₁ ((k ∘ x) ∘ r) (k ∘ (x ∘ r))
    A = comp-assoc r x k
    old : =₁ ((π ∘ (H ∘ x)) ∘ r) ((k ∘ x) ∘ r)
    old = transport-pre π H β x ▷ r
    next : =₁ (π ∘ (H ∘ (x ∘ r))) (k ∘ (x ∘ r))
    next = transport-pre π H β (x ∘ r)
    corner : =₁ (π ∘ ((H ∘ x) ∘ r)) ((π ∘ (H ∘ x)) ∘ r)
    corner = invIso (comp-assoc r (H ∘ x) π)
    edge : =₁ (π ∘ ((H ∘ x) ∘ r)) (π ∘ (H ∘ (x ∘ r)))
    edge = π ◁ comp-assoc r x H
    core : =₂ ((old ∙ corner) ∙ invIso edge) (invIso A ∙ next)
    core = invIso (move-square A (old ∙ corner) next edge
      (transport-pre-assoc π H k β x r ∙ invIso (isoComp-assoc-at A old corner)))

  associator-corner : {R T X Y Z : CAT} (r : MAP R T) (u : MAP T X) (π : MAP X Y) (f : MAP Y Z)
    → =₂ ((comp-assoc u π f ▷ r) ∙ invIso (comp-assoc r u (f ∘ π)))
        ((invIso (comp-assoc r (π ∘ u) f) ∙ (f ◁ invIso (comp-assoc r u π))) ∙ comp-assoc (u ∘ r) π f)
  associator-corner r u π f =
    isoComp-cong (isoComp-cong (idIso (invIso (comp-assoc r (π ∘ u) f))) (invIso (post-inverse f (comp-assoc r u π))))
      (idIso (comp-assoc (u ∘ r) π f)) ∙
    (invIso (isoComp-assoc-at (invIso (comp-assoc r (π ∘ u) f)) (invIso (f ◁ comp-assoc r u π)) (comp-assoc (u ∘ r) π f)) ∙
      invIso (pentagon-left-corner (comp-assoc (u ∘ r) π f) (comp-assoc r u (f ∘ π))
        (f ◁ comp-assoc r u π) (comp-assoc r (π ∘ u) f) (comp-assoc u π f ▷ r)
        (pentagon-whiskered r u π f)))

  unit-corner : {R T E : CAT} (r : MAP R T) (v : MAP T E)
    → =₂ ((comp-unitˡ v ▷ r) ∙ invIso (comp-assoc r v (id E))) (comp-unitˡ (v ∘ r))
  unit-corner r v = cancel-right (comp-assoc r v (id _)) (comp-unitˡ (v ∘ r)) ∙
    isoComp-cong (invIso (left-unitor-comp r v)) (idIso (invIso (comp-assoc r v (id _))))

  composite-normalization-pre : {R T X Y Z W : CAT}
    (π : MAP Y Z) (H : MAP X Y) (q : MAP X W) (f : MAP W Z)
    (β : =₁ (π ∘ H) (f ∘ q)) (u : MAP T X) (r : MAP R T)
    → =₂ (restricted-normalization π H u (comp-assoc u q f ∙ transport-pre π H β u) r)
      ((invIso (comp-assoc r (q ∘ u) f) ∙ (f ◁ invIso (comp-assoc r u q))) ∙
        (comp-assoc (u ∘ r) q f ∙ transport-pre π H β (u ∘ r)))
  composite-normalization-pre π H q f β u r =
    isoComp-assoc-at (invIso (comp-assoc r (q ∘ u) f) ∙ (f ◁ invIso (comp-assoc r u q)))
      (comp-assoc (u ∘ r) q f) (transport-pre π H β (u ∘ r)) ∙
    (isoComp-cong (associator-corner r u q f) (idIso (transport-pre π H β (u ∘ r))) ∙
      normalization-pre π H (f ∘ q) β u r (comp-assoc u q f))

  identity-normalization-pre : {R T Y Z : CAT}
    (π : MAP Y Z) (H : MAP Z Y) (β : =₁ (π ∘ H) (id Z)) (v : MAP T Z) (r : MAP R T)
    → =₂ (restricted-normalization π H v (comp-unitˡ v ∙ transport-pre π H β v) r)
        (comp-unitˡ (v ∘ r) ∙ transport-pre π H β (v ∘ r))
  identity-normalization-pre π H β v r =
    isoComp-cong (unit-corner r v) (idIso (transport-pre π H β (v ∘ r))) ∙
      normalization-pre π H (id _) β v r (comp-unitˡ v)

  project-transport : {X Y Z : CAT} (π : MAP Y Z) {u u′ v v′ : MAP X Y}
    (L : =₁ u u′) (R : =₁ v v′) (σ : =₁ u v)
    → =₂ (π ◁ (R ∙ (σ ∙ invIso L))) ((π ◁ R) ∙ ((π ◁ σ) ∙ invIso (π ◁ L)))
  project-transport π L R σ = isoComp-cong (idIso (π ◁ R))
      (isoComp-cong (idIso (π ◁ σ)) (post-inverse π L) ∙ postWhisker-isoComp-at π σ (invIso L)) ∙
    postWhisker-isoComp-at π R (σ ∙ invIso L)

  extend-square : {X Y : CAT} {u u′ v v′ x y : MAP X Y}
    (L : =₁ u u′) (R : =₁ v v′) (σ : =₁ u v)
    (l : =₁ u x) (r : =₁ v y) (δ : =₁ x y)
    → =₂ (r ∙ σ) (δ ∙ l)
    → =₂ ((r ∙ invIso R) ∙ (R ∙ (σ ∙ invIso L))) (δ ∙ (l ∙ invIso L))
  extend-square L R σ l r δ square = isoComp-assoc-at δ l (invIso L) ∙
    (isoComp-cong square (idIso (invIso L)) ∙
    (invIso (isoComp-assoc-at r σ (invIso L)) ∙
    (isoComp-cong (idIso r) (cancel-left R (σ ∙ invIso L)) ∙
      isoComp-assoc-at r (invIso R) (R ∙ (σ ∙ invIso L)))))

  coordinate-pre : {C D E Z S T : CAT} {F : MAP C E} {G : MAP D E}
    (π : MAP E Z) (t : Cone F G T) (r : MAP S T)
    {x y : MAP T Z} (l : =₁ (π ∘ (F ∘ Cone.left t)) x)
    (q : =₁ (π ∘ (G ∘ Cone.right t)) y)
    {x′ : MAP S Z} (l′ : =₁ (π ∘ (F ∘ (Cone.left t ∘ r))) x′)
    (q′ : =₁ (π ∘ (G ∘ (Cone.right t ∘ r))) (y ∘ r))
    (D′ : =₁ x′ (x ∘ r))
    → =₂ (restricted-normalization π F (Cone.left t) l r) (D′ ∙ l′)
    → =₂ (restricted-normalization π G (Cone.right t) q r) q′
    → =₂ (q′ ∙ ((π ◁ Cone.match (conePre r t)) ∙ invIso l′))
        (((q ∙ ((π ◁ Cone.match t) ∙ invIso l)) ▷ r) ∙ D′)
  coordinate-pre {F = F} {G} π t r {x} {y} l q l′ q′ D′ left right =
    square-to-changeEndpoints l′ q′ (π ◁ Cone.match (conePre r t)) (δ ∙ D′)
      (invIso (isoComp-assoc-at δ D′ l′) ∙
      (isoComp-cong (idIso δ) left ∙
      (extend-square (π ◁ L) (π ◁ R) (π ◁ (Cone.match t ▷ r))
        (transport-pre π (F ∘ Cone.left t) l r) (transport-pre π (G ∘ Cone.right t) q r) δ
        (pre-square-projection π (Cone.match t) edge l q r
          (changeEndpoints-to-square l q (π ◁ Cone.match t) edge (idIso edge))) ∙
      (isoComp-cong (idIso (restricted-normalization π G (Cone.right t) q r)) (project-transport π L R (Cone.match t ▷ r)) ∙
        isoComp-cong (invIso right) (idIso (π ◁ Cone.match (conePre r t)))))))
    where
    edge : =₁ x y
    edge = q ∙ ((π ◁ Cone.match t) ∙ invIso l)
    δ : =₁ (x ∘ r) (y ∘ r)
    δ = edge ▷ r
    L : =₁ ((F ∘ Cone.left t) ∘ r) (F ∘ (Cone.left t ∘ r))
    L = comp-assoc r (Cone.left t) F
    R : =₁ ((G ∘ Cone.right t) ∘ r) (G ∘ (Cone.right t ∘ r))
    R = comp-assoc r (Cone.right t) G
```
