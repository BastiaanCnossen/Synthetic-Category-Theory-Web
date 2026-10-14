# Restricting a projected frame with a specified boundary

Restriction preserves a projected frame together with a comparison of its
boundary. The calculation makes all parameter associators explicit.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.Coordinates.FramedProjectionRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
  using (restricted-normalization; normalization-pre; associator-corner)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (lift-base)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones 𝒯 using (module Coordinate)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (transport-pre)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-right; pre-square-projection)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module Lift {X Y Z Γ Δ : CAT} (g : MAP Y Z) (q : MAP X Y) (h : MAP Γ X)
  {e : MAP Γ Y} (α : (q ∘ h) =₁ e) (t : MAP Δ Γ) where
  last = comp-assoc (h ∘ t) q g
  outer = comp-assoc t h (g ∘ q)
  middle = comp-assoc t (q ∘ h) g
  edge = comp-assoc t e g
  inner = comp-assoc t h q
  first = (g ◁ α) ▷ t
  lifted = g ◁ (α ▷ t)
  correction = g ◁ (inner ⁻¹)

  abstract
    comparison : transport-pre (g ∘ q) h (lift-base g q h α) t =₂
      ((edge ⁻¹ ∙ (g ◁ transport-pre q h α t)) ∙ last)
    comparison = isoComp-cong
      (isoComp-cong (idIso (edge ⁻¹)) ((postWhisker-isoComp-at g (α ▷ t) (inner ⁻¹)) ⁻¹) ∙
        isoComp-assoc-at (edge ⁻¹) lifted correction)
      (idIso last) ∙
      (isoComp-cong
        (isoComp-cong ((move-square edge first lifted middle (whisker-mixed-at α t g)) ⁻¹)
          (idIso correction) ∙ (isoComp-assoc-at first (middle ⁻¹) correction) ⁻¹)
        (idIso last) ∙
      ((isoComp-assoc-at first (middle ⁻¹ ∙ correction) last) ⁻¹ ∙
      (isoComp-cong (idIso first) (associator-corner t h q g) ∙
      (isoComp-assoc-at first (comp-assoc h q g ▷ t) (outer ⁻¹) ∙
        isoComp-cong (preWhisker-isoComp-at (g ◁ α) (comp-assoc h q g) t) (idIso (outer ⁻¹))))))

module At {X Y Z W Γ : CAT} (π : MAP Y Z) (H : MAP X Y) (q : MAP X W)
  (g : MAP W Z) (ζ : (π ∘ H) =₁ (g ∘ q)) (h : MAP Γ X)
  {e : MAP Γ W} (α : (q ∘ h) =₁ e) {v : MAP Γ Z} (κ : (g ∘ e) =₁ v) where
  projected = comp-assoc h q g ∙ transport-pre π H ζ h
  frame = κ ∙ ((g ◁ α) ∙ projected)
  n = κ ∙ lift-base g q h α
  module Projection = Coordinate H H g g q q π ζ ζ using (left-normal; left-natural)

  abstract
    frame-normal : frame =₂ (n ∙ transport-pre π H ζ h)
    frame-normal = (isoComp-assoc-at κ (lift-base g q h α) (transport-pre π H ζ h)) ⁻¹ ∙
      isoComp-cong (idIso κ)
        ((isoComp-assoc-at (g ◁ α) (comp-assoc h q g) (transport-pre π H ζ h)) ⁻¹)

  module Restrict {Δ : CAT} (t : MAP Δ Γ) where
    module Boundary = Lift g q h α t using (comparison)
    boundary = transport-pre q h α t
    vertex = transport-pre g e κ t
    projected-at = comp-assoc (h ∘ t) q g ∙ transport-pre π H ζ (h ∘ t)

    abstract
      outer-normal : transport-pre (g ∘ q) h n t =₂
        ((vertex ∙ (g ◁ boundary)) ∙ comp-assoc (h ∘ t) q g)
      outer-normal = isoComp-cong
          ((isoComp-assoc-at (κ ▷ t) ((comp-assoc t e g) ⁻¹) (g ◁ boundary)) ⁻¹)
          (idIso (comp-assoc (h ∘ t) q g)) ∙
        ((isoComp-assoc-at (κ ▷ t) ((comp-assoc t e g) ⁻¹ ∙ (g ◁ boundary))
          (comp-assoc (h ∘ t) q g)) ⁻¹ ∙
        (isoComp-cong (idIso (κ ▷ t)) Boundary.comparison ∙
        (isoComp-assoc-at (κ ▷ t) (lift-base g q h α ▷ t) ((comp-assoc t h (g ∘ q)) ⁻¹) ∙
          isoComp-cong (preWhisker-isoComp-at κ (lift-base g q h α) t)
            (idIso ((comp-assoc t h (g ∘ q)) ⁻¹)))))

      comparison : restricted-normalization π H h frame t =₂
        (vertex ∙ ((g ◁ boundary) ∙ projected-at))
      comparison = isoComp-assoc-at vertex (g ◁ boundary) projected-at ∙
        (isoComp-assoc-at (vertex ∙ (g ◁ boundary)) (comp-assoc (h ∘ t) q g)
          (transport-pre π H ζ (h ∘ t)) ∙
        (isoComp-cong outer-normal (idIso (transport-pre π H ζ (h ∘ t))) ∙
        (normalization-pre π H (g ∘ q) ζ h t n ∙
          isoComp-cong
            (isoComp-cong (preWhisker t ◁ frame-normal) (idIso ((comp-assoc t (H ∘ h) π) ⁻¹)))
            (idIso ((π ◁ comp-assoc t h H) ⁻¹)))))

    module AtParameter {h′ : MAP Δ X} (θ : (h ∘ t) =₁ h′) where
      boundary′ = boundary ∙ (q ◁ θ) ⁻¹
      source-change = π ◁ (H ◁ θ)
      target-change = g ◁ (q ◁ θ)
      new-projected = Projection.left-normal h′

      abstract
        inverse-route : (projected-at ∙ source-change ⁻¹) =₂
          (target-change ⁻¹ ∙ new-projected)
        inverse-route = (move-square target-change projected-at new-projected source-change
          ((Projection.left-natural θ) ⁻¹)) ⁻¹

        boundary-image : ((g ◁ boundary) ∙ target-change ⁻¹) =₂ (g ◁ boundary′)
        boundary-image = (postWhisker-isoComp-at g boundary ((q ◁ θ) ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso (g ◁ boundary)) ((post-inverse g (q ◁ θ)) ⁻¹)

        changed-comparison :
          (restricted-normalization π H h frame t ∙ source-change ⁻¹) =₂
          (vertex ∙ ((g ◁ boundary′) ∙ new-projected))
        changed-comparison = isoComp-cong (idIso vertex)
            (isoComp-cong boundary-image (idIso new-projected)) ∙
          (isoComp-cong (idIso vertex)
            ((isoComp-assoc-at (g ◁ boundary) (target-change ⁻¹) new-projected) ⁻¹) ∙
          (isoComp-cong (idIso vertex) (isoComp-cong (idIso (g ◁ boundary)) inverse-route) ∙
          (isoComp-cong (idIso vertex)
            (isoComp-assoc-at (g ◁ boundary) projected-at (source-change ⁻¹)) ∙
          (isoComp-assoc-at vertex ((g ◁ boundary) ∙ projected-at) (source-change ⁻¹) ∙
            isoComp-cong comparison (idIso (source-change ⁻¹))))))
```

A frame with no final boundary comparison has a simpler restriction law.
This is the identity-boundary specialization of the preceding calculation.

```agda
module BoundaryOnly {X Y Z W Γ : CAT} (π : MAP Y Z) (H : MAP X Y) (q : MAP X W)
  (g : MAP W Z) (ζ : (π ∘ H) =₁ (g ∘ q)) (h : MAP Γ X)
  {e : MAP Γ W} (α : (q ∘ h) =₁ e) where
  private
    module Framed = At π H q g ζ h α (idIso (g ∘ e))
      using (module Restrict)
  frame = (g ◁ α) ∙ (comp-assoc h q g ∙ transport-pre π H ζ h)

  abstract
    restriction : {Δ : CAT} (t : MAP Δ Γ) →
      restricted-normalization π H h frame t =₂
        ((comp-assoc t e g) ⁻¹ ∙ ((g ◁ transport-pre q h α t) ∙
          (comp-assoc (h ∘ t) q g ∙ transport-pre π H ζ (h ∘ t))))
    restriction t = isoComp-cong vertex-id (idIso _) ∙
      (Framed.Restrict.comparison t ∙
        isoComp-cong
          (isoComp-cong (preWhisker t ◁ (isoComp-unitˡ-at frame) ⁻¹)
            (idIso ((comp-assoc t (H ∘ h) π) ⁻¹)))
          (idIso ((π ◁ comp-assoc t h H) ⁻¹)))
      where
      vertex-id : Framed.Restrict.vertex t =₂ (comp-assoc t e g) ⁻¹
      vertex-id = isoComp-unitˡ-at ((comp-assoc t e g) ⁻¹) ∙
        isoComp-cong (preWhisker-idIso (g ∘ e) t) (idIso ((comp-assoc t e g) ⁻¹))
```


A specified identification of a family into the target can be read through
a coordinate triangle. After restriction, the decoded boundary is the
restricted original coordinate boundary, with the displayed associator.
The identification and its coordinate triangle are retained as inputs.

```agda
module AlongIdentification {X Y Z W B : CAT}
  (π : MAP Y Z) (H : MAP X Y) (q : MAP X W) (g : MAP W Z)
  (ζ : (π ∘ H) =₁ (g ∘ q)) (family : MAP B X)
  {e : MAP B W} (α : (q ∘ family) =₁ e)
  (target : MAP B Y) (β : (π ∘ target) =₁ (g ∘ e))
  (δ : (H ∘ family) =₁ target) where
  private
    module Frame = BoundaryOnly π H q g ζ family α using (frame; restriction)
    module Projection = Coordinate H H g g q q π ζ ζ using (left-normal)

  module Restrict (triangle : (β ∙ (π ◁ δ)) =₂ Frame.frame)
    {Γ : CAT} (r : MAP Γ B) where
    family-change : (H ∘ (family ∘ r)) =₁ (target ∘ r)
    family-change = (δ ▷ r) ∙ (comp-assoc r family H) ⁻¹
    decoded : (g ∘ (q ∘ (family ∘ r))) =₁ ((g ∘ e) ∘ r)
    decoded = transport-pre π target β r ∙
      ((π ◁ family-change) ∙ (Projection.left-normal (family ∘ r)) ⁻¹)
    restricted : (g ∘ (q ∘ (family ∘ r))) =₁ ((g ∘ e) ∘ r)
    restricted = (comp-assoc r e g) ⁻¹ ∙ (g ◁ transport-pre q family α r)

    abstract
      comparison : decoded =₂ restricted
      comparison = cancel-right (Projection.left-normal (family ∘ r)) restricted ∙
        (isoComp-cong normalized (idIso ((Projection.left-normal (family ∘ r)) ⁻¹)) ∙
          (isoComp-assoc-at (transport-pre π target β r) (π ◁ family-change)
            ((Projection.left-normal (family ∘ r)) ⁻¹)) ⁻¹)
        where
        moved : (transport-pre π target β r ∙ (π ◁ (δ ▷ r))) =₂
          transport-pre π (H ∘ family) Frame.frame r
        moved = isoComp-unitˡ-at (transport-pre π (H ∘ family) Frame.frame r) ∙
          (isoComp-cong (preWhisker-idIso (g ∘ e) r)
            (idIso (transport-pre π (H ∘ family) Frame.frame r)) ∙
          pre-square-projection π δ (idIso (g ∘ e)) Frame.frame β r
            ((isoComp-unitˡ-at Frame.frame) ⁻¹ ∙ triangle))
        projection : (transport-pre π target β r ∙ (π ◁ family-change)) =₂
          restricted-normalization π H family Frame.frame r
        projection = isoComp-cong moved (idIso ((π ◁ comp-assoc r family H) ⁻¹)) ∙
          ((isoComp-assoc-at (transport-pre π target β r) (π ◁ (δ ▷ r))
            ((π ◁ comp-assoc r family H) ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso (transport-pre π target β r))
            (isoComp-cong (idIso (π ◁ (δ ▷ r))) (post-inverse π (comp-assoc r family H)) ∙
              postWhisker-isoComp-at π (δ ▷ r) ((comp-assoc r family H) ⁻¹)))
        normalized : (transport-pre π target β r ∙ (π ◁ family-change)) =₂
          (restricted ∙ Projection.left-normal (family ∘ r))
        normalized = (isoComp-assoc-at ((comp-assoc r e g) ⁻¹)
          (g ◁ transport-pre q family α r) (Projection.left-normal (family ∘ r))) ⁻¹ ∙
          (Frame.restriction r ∙ projection)
```
