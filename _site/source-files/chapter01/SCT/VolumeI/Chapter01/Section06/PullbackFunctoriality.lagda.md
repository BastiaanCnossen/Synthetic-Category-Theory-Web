# Pullbacks under maps of cospans

A map of cospans consists of three functors and the two specified squares.
Its action on a cone pastes those squares with the original matching.
The induced pullback map factors that actual cone; its beta retains the
complete matching compatibility.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; id₌; inv₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-prefix-assoc; comp₌-unitʳ-One; comp₌-inverseˡ-One; preWhisker-inverse)
import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses as InverseLaws
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
open import SCT.VolumeI.Chapter01.Section06.ConePasting
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange
open import SCT.VolumeI.Chapter01.Section06.PastingLemma

module _ {Γ : Context} where
  record CospanMap {C D E C′ D′ E′ : CAT Γ}
    (f : MAP C E) (g : MAP D E) (f′ : MAP C′ E′) (g′ : MAP D′ E′) : Set m where
    field
      left : MAP C C′
      right : MAP D D′
      base : MAP E E′
      left-square : (f′ ∘ left) =₁ (base ∘ f)
      right-square : (g′ ∘ right) =₁ (base ∘ g)

    private
      left-route : {T : CAT Γ} (p : MAP T C)
        → (f′ ∘ (left ∘ p)) =₁ (base ∘ (f ∘ p))
      left-route p = comp-assoc p f base ∙
        ((left-square ▷ p) ∙ (comp-assoc p left f′) ⁻¹)

      finish-right : {T : CAT Γ} (p : MAP T C) (q : MAP T D)
        → (f′ ∘ (left ∘ p)) =₁ (base ∘ (g ∘ q))
        → (f′ ∘ (left ∘ p)) =₁ (g′ ∘ (right ∘ q))
      finish-right p q τ = comp-assoc q right g′ ∙
        ((right-square ⁻¹ ▷ q) ∙ ((comp-assoc q g base) ⁻¹ ∙ τ))

    map-cone : {T : CAT Γ} → Cone f g T → Cone f′ g′ T
    map-cone s = record
      { left = left ∘ Cone.left s
      ; right = right ∘ Cone.right s
      ; match = finish-right (Cone.left s) (Cone.right s)
          ((base ◁ Cone.match s) ∙ left-route (Cone.left s)) }

  cospan-right-cone : {C D E C′ D′ E′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    (F : CospanMap f g f′ g′) → Cone g′ (CospanMap.base F) D
  cospan-right-cone {g = g} F = record
    { left = CospanMap.right F; right = g; match = CospanMap.right-square F }

  pullback-map : {C D E C′ D′ E′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    → CospanMap f g f′ g′ → MAP (Pullback f g) (Pullback f′ g′)
  pullback-map {f = f} {g} F = pullback-factor (CospanMap.map-cone F (pullback-cone f g))

  pullback-map-β : {C D E C′ D′ E′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    (F : CospanMap f g f′ g′)
    → ConeIdentification₁ (cone-restrict (pullback-map F) (pullback-cone f′ g′))
        (CospanMap.map-cone F (pullback-cone f g))
  pullback-map-β {f = f} {g} F = pullback-factor-β (CospanMap.map-cone F (pullback-cone f g))
```

## Cartesian maps of cospans

When the specified right square is a pullback, so is the square on the left
projections. The comparison uses the actual mapped-cone beta and the general
pasting of a factor cone. Left-arrow change is normalized explicitly from
its symmetry-based matching. No identity or composition law for cospan maps
is assumed. The equivalence corollaries expose their proof only; the
full projection geometry remains available through CartesianProjection.
Their proofs are opaque, so specializing them does not expand the entire
pasting argument.

```agda
module _ {Γ : Context} where
  module CartesianProjection {C D E C′ D′ E′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    (F : CospanMap f g f′ g′)
    (right-pullback : IsPullback (cospan-right-cone F)) where

    open CospanMap F renaming (left to u; right to v; base to w; left-square to α; right-square to β)
    source : Cone f g (Pullback f g)
    source = pullback-cone f g
    target : Cone f′ g′ (Pullback f′ g′)
    target = pullback-cone f′ g′
    p : MAP (Pullback f g) C
    p = Cone.left source
    q : MAP (Pullback f g) D
    q = Cone.right source
    H : MAP (Pullback f g) (Pullback f′ g′)
    H = pullback-map F
    legLeft : (Cone.left target ∘ H) =₁ (u ∘ p)
    legLeft = ConeIdentification₁.left (pullback-map-β F)
    ρ : (Cone.right target ∘ H) =₁ (v ∘ q)
    ρ = ConeIdentification₁.right (pullback-map-β F)
    σ : (f′ ∘ (u ∘ p)) =₁ (g′ ∘ (v ∘ q))
    σ = Cone.match (map-cone source)

    right-square : Cone g′ w D
    right-square = record { left = v ; right = g ; match = β }
    rightCone : Cone w g′ D
    rightCone = cone-swap right-square
    right-isPullback : IsPullback rightCone
    right-isPullback = SwappedCone.isPullback right-square right-pullback
    module RightPaste = Pasting f w g′ rightCone right-isPullback
    pasted : Cone (w ∘ f) g′ (Pullback f g)
    pasted = RightPaste.Paste.paste source
    changed : Cone (f′ ∘ u) g′ (Pullback f g)
    changed = cone-change-left (α ⁻¹) pasted

    outerMapped : Cone (f′ ∘ u) g′ (Pullback f g)
    outerMapped = record { left = p ; right = v ∘ q ; match = σ ∙ comp-assoc p u f′ }

    changed-cone-law : ConeIdentification₁ changed outerMapped
    changed-cone-law = cone-retarget-match-identification changed (Cone.match outerMapped)
      (normalized ⁻¹ ∙
        (comp₌-cong (id₌ (Cone.match pasted)) (InverseLaws.inverse-inverse (α ▷ p) ∙ (inv₌ ◁ preWhisker-inverse α p)) ∙
          cone-change-left-matching (α ⁻¹) pasted))
      where
      ar : ((g′ ∘ v) ∘ q) =₁ (g′ ∘ (v ∘ q))
      ar = comp-assoc q v g′
      br : ((w ∘ g) ∘ q) =₁ ((g′ ∘ v) ∘ q)
      br = β ⁻¹ ▷ q
      cr : (w ∘ (g ∘ q)) =₁ ((w ∘ g) ∘ q)
      cr = (comp-assoc q g w) ⁻¹
      dr : (w ∘ (f ∘ p)) =₁ (w ∘ (g ∘ q))
      dr = w ◁ Cone.match source
      er : ((w ∘ f) ∘ p) =₁ (w ∘ (f ∘ p))
      er = comp-assoc p f w
      fr : ((f′ ∘ u) ∘ p) =₁ ((w ∘ f) ∘ p)
      fr = α ▷ p
      assocLeft : ((f′ ∘ u) ∘ p) =₁ (f′ ∘ (u ∘ p))
      assocLeft = comp-assoc p u f′
      prefix : (w ∘ (g ∘ q)) =₁ (g′ ∘ (v ∘ q))
      prefix = ar ∙ (br ∙ cr)
      σ-normal : σ =₂ ((Cone.match pasted ∙ fr) ∙ assocLeft ⁻¹)
      σ-normal = (comp₌-assoc (Cone.match pasted) fr (assocLeft ⁻¹)) ⁻¹ ∙
        ((comp₌-assoc prefix (dr ∙ er) (fr ∙ assocLeft ⁻¹)) ⁻¹ ∙
        (comp₌-cong (id₌ prefix) ((comp₌-assoc dr er (fr ∙ assocLeft ⁻¹)) ⁻¹) ∙
          comp₌-prefix-assoc ar br cr (dr ∙ (er ∙ (fr ∙ assocLeft ⁻¹)))))
      normalized : (σ ∙ assocLeft) =₂ (Cone.match pasted ∙ fr)
      normalized = comp₌-unitʳ-One (Cone.match pasted ∙ fr) ∙
        (comp₌-cong (id₌ (Cone.match pasted ∙ fr)) (comp₌-inverseˡ-One assocLeft) ∙
        (comp₌-assoc (Cone.match pasted ∙ fr) (assocLeft ⁻¹) assocLeft ∙
          comp₌-cong σ-normal (id₌ assocLeft)))

    outer-isPullback : IsPullback outerMapped
    outer-isPullback = isPullback-cone-identification changed-cone-law
      (ChangeLeftArrow.preserve-pullback (α ⁻¹) g′ pasted
        (RightPaste.paste-isPullback source (pullback-cone-isPullback f g)))

    projectionSquare : Cone u (Cone.left target) (Pullback f g)
    projectionSquare = record { left = p ; right = H ; match = legLeft ⁻¹ }
    module TargetPaste = Pasting u f′ g′ target (pullback-cone-isPullback f′ g′)

    -- The beta retains its literal leg images. Only its target matching is
    -- normalized, cancelling the associator introduced by postcomposition.
    projection-factor-law : ConeIdentification₁ (cone-restrict H target)
      (postcompose-cone-left u f′ outerMapped)
    projection-factor-law = record
      { left = legLeft; right = ρ
      ; compatible = ConeIdentification₁.compatible (pullback-map-β F) ∙
          comp₌-cong (comp-inv-right σ (comp-assoc p u f′)) (id₌ (f′ ◁ legLeft)) }

    outer-cone-law : ConeIdentification₁ (TargetPaste.Paste.paste projectionSquare) outerMapped
    outer-cone-law = TargetPaste.Paste.paste-factor outerMapped H projection-factor-law

    projection-square-isPullback : IsPullback projectionSquare
    projection-square-isPullback = TargetPaste.unpaste-isPullback projectionSquare
      (isPullback-cone-identification (cone-inverse outer-cone-law) outer-isPullback)

  module CospanCartesian {C D E C′ D′ E′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    (F : CospanMap f g f′ g′) (eu : IsEquiv (CospanMap.left F))
    (right-pullback : IsPullback (cospan-right-cone F)) where
    private
      module Projection = CartesianProjection F right-pullback
        using (projectionSquare; projection-square-isPullback)

    opaque
      pullback-map-isEquiv : IsEquiv (pullback-map F)
      pullback-map-isEquiv = left-isEquiv-from-isPullback eu (cone-swap Projection.projectionSquare)
        (SwappedCone.isPullback Projection.projectionSquare Projection.projection-square-isPullback)

  module CospanEquivalence {C D E C′ D′ E′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    (F : CospanMap f g f′ g′) (eu : IsEquiv (CospanMap.left F))
    (ev : IsEquiv (CospanMap.right F)) (ew : IsEquiv (CospanMap.base F)) where

    opaque
      pullback-map-isEquiv : IsEquiv (pullback-map F)
      pullback-map-isEquiv = CospanCartesian.pullback-map-isEquiv F eu
        (isPullback-from-left-isEquiv ew (cospan-right-cone F) ev)
```
