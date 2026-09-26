# From restriction cones to endpoint cones

Evaluation at the terminal domain sends a cone of restriction maps to a
cone of endpoint evaluations. The leg maps and their comparisons remain
the same; the matching is transported through the displayed endpoint
comparisons. Naturality proves the compatibility for a whole cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IP

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.EndpointRestrictionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (post-square; transport-square)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection; move-square)
open IP vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc)

open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; pre-inverse)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.TransposedEndpointFrames as Frames
open Frames.FrameCalculus 𝒯 M ℱ P using (quotient-pre)

open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
  using (changeEndpoints; changeEndpoints-cong; square-to-changeEndpoints)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (changeEndpoints-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module TransportCalculus where
  abstract
    boundaries : {X Y : CAT} {a a′ b b′ : MAP X Y}
      {p p′ : a =₁ a′} {q q′ : b =₁ b′} (α : a =₁ b) →
      p =₂ p′ → q =₂ q′ → changeEndpoints p q α =₂ changeEndpoints p′ q′ α
    boundaries α left right = isoComp-cong right (isoComp-cong (idIso α) (＝-inv ◁ left))

    post : {X Y Z : CAT} (F : MAP Y Z) {a a′ b b′ : MAP X Y}
      (p : a =₁ a′) (q : b =₁ b′) (α : a =₁ b) →
      (F ◁ changeEndpoints p q α) =₂ changeEndpoints (F ◁ p) (F ◁ q) (F ◁ α)
    post F p q α = isoComp-cong (idIso (F ◁ q))
      (isoComp-cong (idIso (F ◁ α)) (post-inverse F p) ∙
        postWhisker-isoComp-at F α (p ⁻¹)) ∙ postWhisker-isoComp-at F q (α ∙ p ⁻¹)

    pre : {W X Y : CAT} (H : MAP W X) {a a′ b b′ : MAP X Y}
      (p : a =₁ a′) (q : b =₁ b′) (α : a =₁ b) →
      (changeEndpoints p q α ▷ H) =₂ changeEndpoints (p ▷ H) (q ▷ H) (α ▷ H)
    pre H p q α = isoComp-cong (idIso (q ▷ H))
      (isoComp-cong (idIso (α ▷ H)) (pre-inverse p H) ∙
        preWhisker-isoComp-at α (p ⁻¹) H) ∙ preWhisker-isoComp-at q (α ∙ p ⁻¹) H

module Endpoints (C : CAT) where
  open PointBoundary C
  e = point-evaluation

  component : {Γ A : CAT} (x : Obj-abs A) (h : MAP Γ (Fun A C)) →
    (e ∘ (funPre x ∘ h)) =₁ (evaluate x ∘ h)
  component x h = transport-pre e (funPre x) (boundary x) h

  abstract
    component-natural : {Γ A : CAT} (x : Obj-abs A)
      {h k : MAP Γ (Fun A C)} (δ : h =₁ k) →
      (component x k ∙ (e ◁ (funPre x ◁ δ))) =₂
        ((evaluate x ◁ δ) ∙ component x h)
    component-natural x δ = substitution-square-projection e (funPre x)
      (evaluate x) (boundary x) δ

    component-pre : {Γ Δ A : CAT} (x : Obj-abs A)
      (h : MAP Γ (Fun A C)) (H : MAP Δ Γ) →
      (component x (h ∘ H) ∙ (e ◁ comp-assoc H h (funPre x))) =₂
        ((comp-assoc H h (evaluate x) ∙ (component x h ▷ H)) ∙
          (comp-assoc H (funPre x ∘ h) e) ⁻¹)
    component-pre x h H = (transport-pre-assoc e (funPre x)
      (evaluate x) (boundary x) h H) ⁻¹

  convert : {Γ A B : CAT} {u : Obj-abs A} {v : Obj-abs B} →
    Cone (funPre {D = C} u) (funPre v) Γ → Cone (evaluate u) (evaluate v) Γ
  convert {u = u} {v} t = record
    { left = Cone.left t ; right = Cone.right t
    ; match = component v (Cone.right t) ∙
        ((e ◁ Cone.match t) ∙ (component u (Cone.left t)) ⁻¹) }

  convertIso : {Γ A B : CAT} {u : Obj-abs A} {v : Obj-abs B}
    {s t : Cone (funPre {D = C} u) (funPre v) Γ} →
    ConeIso s t → ConeIso (convert s) (convert t)
  convertIso {u = u} {v} {s} {t} Φ = record
    { leftIso = ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
    ; compatible = transport-square
        (component u (Cone.left s)) (component u (Cone.left t))
        (component v (Cone.right s)) (component v (Cone.right t))
        (e ◁ Cone.match s) (e ◁ Cone.match t)
        (e ◁ (funPre u ◁ ConeIso.leftIso Φ))
        (e ◁ (funPre v ◁ ConeIso.rightIso Φ))
        (evaluate u ◁ ConeIso.leftIso Φ) (evaluate v ◁ ConeIso.rightIso Φ)
        (component-natural u (ConeIso.leftIso Φ))
        (component-natural v (ConeIso.rightIso Φ))
        (post-square e _ _ _ _ (ConeIso.compatible Φ)) }
```

After this conversion, a corner specified by two endpoint frames has
exactly the quotient of their evaluated frames as its matching.

```agda
  frame : {Γ A : CAT} (u : Obj-abs A) (h : MAP Γ (Fun A C))
    {z : MAP Γ (Fun One C)} → (funPre u ∘ h) =₁ z →
    (evaluate u ∘ h) =₁ (e ∘ z)
  frame u h α = (e ◁ α) ∙ (component u h) ⁻¹

  abstract
    frame-matching : {Γ A B : CAT} (u : Obj-abs A) (v : Obj-abs B)
      (h : MAP Γ (Fun A C)) (k : MAP Γ (Fun B C))
      {z : MAP Γ (Fun One C)} (α : (funPre u ∘ h) =₁ z) (β : (funPre v ∘ k) =₁ z) →
      (component v k ∙ ((e ◁ (β ⁻¹ ∙ α)) ∙ (component u h) ⁻¹)) =₂
        ((frame v k β) ⁻¹ ∙ frame u h α)
    frame-matching u v h k α β =
      (quotient-pre (e ◁ α) (e ◁ β) ((component u h) ⁻¹) ((component v k) ⁻¹)) ⁻¹ ∙
      isoComp-cong ((inverse-inverse (component v k)) ⁻¹)
        (isoComp-cong
          (isoComp-cong (post-inverse e β) (idIso (e ◁ α)) ∙
            postWhisker-isoComp-at e (β ⁻¹) α)
          (idIso ((component u h) ⁻¹)))

  module Parameter {Γ Δ A B : CAT} {u : Obj-abs A} {v : Obj-abs B}
    (H : MAP Δ Γ) (t : Cone (funPre {D = C} u) (funPre v) Γ) where
    l = Cone.left t
    r = Cone.right t
    τ = Cone.match t
    bl = component u l
    br = component v r
    blH = component u (l ∘ H)
    brH = component v (r ∘ H)
    al = comp-assoc H l (funPre u)
    ar = comp-assoc H r (funPre v)
    el = comp-assoc H l (evaluate u)
    er = comp-assoc H r (evaluate v)
    il = comp-assoc H (funPre u ∘ l) e
    ir = comp-assoc H (funPre v ∘ r) e
    raw = e ◁ (τ ▷ H)
    lifted = (e ◁ τ) ▷ H

    abstract
      middle : changeEndpoints (il ⁻¹) (ir ⁻¹) raw =₂ lifted
      middle = square-to-changeEndpoints (il ⁻¹) (ir ⁻¹) raw lifted
        (move-square ir lifted raw il (whisker-mixed-at τ H e))

      matching : (Cone.match (convert (conePre H t))) =₂
        (Cone.match (conePre H (convert t)))
      matching =
        changeEndpoints-cong el er ((TransportCalculus.pre H bl br (e ◁ τ)) ⁻¹) ∙
        (changeEndpoints-cong el er (changeEndpoints-cong (bl ▷ H) (br ▷ H) middle) ∙
        (changeEndpoints-cong el er
          (changeEndpoints-compose (il ⁻¹) (bl ▷ H) (ir ⁻¹) (br ▷ H) raw) ∙
        (changeEndpoints-compose ((bl ▷ H) ∙ il ⁻¹) el ((br ▷ H) ∙ ir ⁻¹) er raw ∙
        (TransportCalculus.boundaries raw
          (isoComp-assoc-at el (bl ▷ H) (il ⁻¹) ∙ component-pre u l H)
          (isoComp-assoc-at er (br ▷ H) (ir ⁻¹) ∙ component-pre v r H) ∙
        ((changeEndpoints-compose (e ◁ al) blH (e ◁ ar) brH raw) ⁻¹ ∙
          changeEndpoints-cong blH brH (TransportCalculus.post e al ar (τ ▷ H)))))))

    comparison : ConeIso (convert (conePre H t)) (conePre H (convert t))
    comparison = cone-match-change _ _ _ _ matching
```

The following comparison uses those same endpoint lifts on the target
of a transposed corner. Its source is the converted restriction
cone. `EndpointCornerComparison` and `EndpointCornerFamilies` identify
this source with the corresponding chosen endpoint cone.

```agda
module Framed {Γ A B C : CAT}
  (f : MAP A (Fun Γ C)) (g : MAP B (Fun Γ C))
  (u : Obj-abs A) (v : Obj-abs B) (z : Obj-abs (Fun Γ C))
  (α : (f ∘ u) =₁ z) (β : (g ∘ v) =₁ z) where
  open Endpoints C
  module Raw = Frames.FramedCorner 𝒯 M ℱ P f g u v z α β
  left-frame = frame u Raw.Left.family Raw.left-frame
  right-frame = frame v Raw.Right.family Raw.right-frame

  target : Cone (evaluate u) (evaluate v) Γ
  target = record
    { left = Raw.Left.family ; right = Raw.Right.family
    ; match = right-frame ⁻¹ ∙ left-frame }

  abstract
    matching : (Cone.match (convert Raw.Curried.value)) =₂ (Cone.match target)
    matching = frame-matching u v Raw.Left.family Raw.Right.family
      Raw.left-frame Raw.right-frame ∙
      isoComp-cong (idIso (component v Raw.Right.family))
        (isoComp-cong (postWhisker e ◁ Raw.matching)
          (idIso ((component u Raw.Left.family) ⁻¹)))

  comparison : {s : Cone (funPre {D = C} u) (funPre v) Γ} →
    ConeIso s Raw.Curried.value → ConeIso (convert s) target
  comparison Φ = record
    { leftIso = ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
    ; compatible = ConeIso.compatible (convertIso Φ) ∙
        isoComp-cong (matching ⁻¹) (idIso (evaluate u ◁ ConeIso.leftIso Φ)) }
```
