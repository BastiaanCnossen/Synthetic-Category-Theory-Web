# Pairing specified vertex frame squares

Two vertex squares induce the paired square, retaining the chosen
pair-pre comparisons on both sides. These are the same finite calculations
already checked privately in Triangles. This offsource extraction is for
the endpoint assembly; canonical adoption should share the existing owner,
rather than retain two independent copies.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.PairedVertexFrames where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction

module PairedRestrictionImage {Γ : Context} {A P T C D : CAT Γ}
  (source : MAP A C) (target : MAP A D) (π : MAP P A) (q : MAP T P)
  (edge : MAP T A) (δ : (π ∘ q) =₁ edge)
  {x : MAP T C} {y : MAP T D}
  (left-frame : (source ∘ edge) =₁ x)
  (right-frame : (target ∘ edge) =₁ y) where
  private
    left = left-frame ∙ (source ◁ δ)
    right = right-frame ∙ (target ◁ δ)
    left-assoc = comp-assoc q π source
    right-assoc = comp-assoc q π target
    chosen-left = left-frame ∙ ((source ◁ δ) ∙ left-assoc)
    chosen-right = right-frame ∙ ((target ◁ δ) ∙ right-assoc)
    paired = pair⁼ left right
    associators = pair⁼ left-assoc right-assoc
    restricted = pair-pre (source ∘ π) (target ∘ π) q
    first-restriction = pair-pre source target π ▷ q
    together = pair-pre source target (π ∘ q)
    associator = comp-assoc q π (pair source target)

    normalize-frames : pair⁼ chosen-left chosen-right =₂ (paired ∙ associators)
    normalize-frames = pair⁼-comp left left-assoc right right-assoc ∙
      pair⁼-cong ((comp₌-assoc left-frame (source ◁ δ) left-assoc) ⁻¹)
        ((comp₌-assoc right-frame (target ◁ δ) right-assoc) ⁻¹)

  image : ((pair⁼ chosen-left chosen-right ∙ restricted) ∙ first-restriction) =₂
    ((paired ∙ together) ∙ associator)
  image = (comp₌-assoc paired together associator) ⁻¹ ∙
    (comp₌-cong (id₌ paired) ((pair-pre-iterated source target π q) ⁻¹) ∙
      (comp₌-assoc paired associators (restricted ∙ first-restriction) ∙
        (comp₌-assoc (paired ∙ associators) restricted first-restriction ∙
          comp₌-cong (comp₌-cong normalize-frames (id₌ restricted))
            (id₌ first-restriction))))

module _ {Γ : Context} where
  pair-action-image : {K C D T : CAT Γ} (f : MAP K C) (g : MAP K D)
    {r s : MAP T K} (δ : r =₁ s) {x : MAP T C} {y : MAP T D}
    (b : (f ∘ s) =₁ x) (d : (g ∘ s) =₁ y)
    → ((pair⁼ b d ∙ pair-pre f g s) ∙ (pair f g ◁ δ)) =₂
        (pair⁼ (b ∙ (f ◁ δ)) (d ∙ (g ◁ δ)) ∙ pair-pre f g r)
  pair-action-image f g {r} δ b d =
    comp₌-cong (id₌ paired)
      (comp₌-unitˡ-One together ∙
        comp₌-cong (pair⁼-id-One (f ∘ r) (g ∘ r)) (id₌ together)) ∙
      pair-evaluation-natural-One f g δ (id₌ (f ∘ r)) b (id₌ (g ∘ r)) d
        (b ∙ (f ◁ δ)) (d ∙ (g ◁ δ))
        ((comp₌-unitʳ-One (b ∙ (f ◁ δ))) ⁻¹)
        ((comp₌-unitʳ-One (d ∙ (g ◁ δ))) ⁻¹)
    where
      paired = pair⁼ (b ∙ (f ◁ δ)) (d ∙ (g ◁ δ))
      together = pair-pre f g r

  paired-input-image : {P T C D : CAT Γ}
    {x x′ : MAP P C} {y y′ : MAP P D}
    (u : x =₁ x′) (v : y =₁ y′) (q : MAP T P)
    {z : MAP T C} {w : MAP T D}
    (b : (x ∘ q) =₁ z) (b′ : (x′ ∘ q) =₁ z)
    (d : (y ∘ q) =₁ w) (d′ : (y′ ∘ q) =₁ w)
    → (b′ ∙ (u ▷ q)) =₂ b → (d′ ∙ (v ▷ q)) =₂ d
    → ((pair⁼ b′ d′ ∙ pair-pre x′ y′ q) ∙ (pair⁼ u v ▷ q)) =₂
        (pair⁼ b d ∙ pair-pre x y q)
  paired-input-image {x = x} {y = y} u v q {z} {w} b b′ d d′ left right =
    comp₌-unitˡ-One before ∙
      (comp₌-cong (pair⁼-id-One z w) (id₌ before) ∙
        pair-evaluation-natural-inputs-One u v q b b′ d d′ (id₌ z) (id₌ w)
          (((comp₌-unitˡ-One b) ⁻¹) ∙ left)
          (((comp₌-unitˡ-One d) ⁻¹) ∙ right))
    where before = pair⁼ b d ∙ pair-pre x y q

module PairedBaseImage {Γ : Context} {P T K C D : CAT Γ}
  (f : MAP K C) (g : MAP K D) (baseP : MAP P K) (q : MAP T P)
  (baseT : MAP T K) (δ : (baseP ∘ q) =₁ baseT)
  {x : MAP P C} {y : MAP P D} {x′ : MAP T C} {y′ : MAP T D}
  (old-left : (f ∘ baseP) =₁ x) (old-right : (g ∘ baseP) =₁ y)
  (new-left : (f ∘ baseT) =₁ x′) (new-right : (g ∘ baseT) =₁ y′)
  (left-frame : (x ∘ q) =₁ x′) (right-frame : (y ∘ q) =₁ y′)
  (left-square : (new-left ∙ ((f ◁ δ) ∙ comp-assoc q baseP f)) =₂
    (left-frame ∙ (old-left ▷ q)))
  (right-square : (new-right ∙ ((g ◁ δ) ∙ comp-assoc q baseP g)) =₂
    (right-frame ∙ (old-right ▷ q))) where
  private
    module Inner = PairedRestrictionImage f g baseP q baseT δ new-left new-right
    old-pair = pair⁼ old-left old-right ∙ pair-pre f g baseP
    new-pair = pair⁼ new-left new-right ∙ pair-pre f g baseT
    projected = pair⁼ left-frame right-frame ∙ pair-pre x y q
    chosen-left = new-left ∙ ((f ◁ δ) ∙ comp-assoc q baseP f)
    chosen-right = new-right ∙ ((g ◁ δ) ∙ comp-assoc q baseP g)
    restricted = pair-pre (f ∘ baseP) (g ∘ baseP) q
    first-restriction = pair-pre f g baseP ▷ q
    associator = comp-assoc q baseP (pair f g)
    paired = pair⁼ (new-left ∙ (f ◁ δ)) (new-right ∙ (g ◁ δ))
    together = pair-pre f g (baseP ∘ q)
    frame-image = paired-input-image old-left old-right q
      chosen-left left-frame chosen-right right-frame (left-square ⁻¹) (right-square ⁻¹)

  image : (new-pair ∙ ((pair f g ◁ δ) ∙ associator)) =₂
    (projected ∙ (old-pair ▷ q))
  image = comp₌-cong (id₌ projected)
      ((preWhisker-comp₌ (pair⁼ old-left old-right) (pair-pre f g baseP) q) ⁻¹) ∙
    (comp₌-assoc projected (pair⁼ old-left old-right ▷ q) first-restriction ∙
      (comp₌-cong (frame-image ⁻¹) (id₌ first-restriction) ∙
        ((Inner.image) ⁻¹ ∙
          (comp₌-cong (pair-action-image f g δ new-left new-right) (id₌ associator) ∙
            (comp₌-assoc new-pair (pair f g ◁ δ) associator) ⁻¹))))
```
