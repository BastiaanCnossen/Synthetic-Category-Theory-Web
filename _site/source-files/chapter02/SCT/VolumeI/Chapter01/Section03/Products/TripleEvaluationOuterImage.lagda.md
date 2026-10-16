# Outer vertices of a framed triple evaluation

A paired triple of vertex triangles carries its first and last vertices
by the paired evaluation of those same two triangles. This computes the
actual chosen base cell, including its associator, rather than replacing
it with another cell with equal endpoints.

This offsource candidate reuses the existing private restriction helpers
from Triangles verbatim. Canonical adoption should share their owner and
not retain duplicated helper code. The public computation below applies
both to the prescribed composable pair and to the short-edge map.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.TripleEvaluationOuterImage where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; preWhisker-id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; post-triangle; unrestrict-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction

private
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

  module NestedVertexImage {Γ : Context} {P T K E B : CAT Γ}
    (π : MAP E B) (baseP : MAP P K) (q : MAP T P) (baseT : MAP T K)
    (δ : (baseP ∘ q) =₁ baseT) (r : MAP K E)
    {u : MAP P E} {v : MAP T E} {x : MAP P B} {y : MAP T B}
    (old : (r ∘ baseP) =₁ u) (new : (r ∘ baseT) =₁ v)
    (edge : (u ∘ q) =₁ v)
    (old-inner : (π ∘ u) =₁ x) (new-inner : (π ∘ v) =₁ y)
    (inner : (x ∘ q) =₁ y)
    (outer-square : (new ∙ (r ◁ δ)) =₂ (edge ∙ restrict-triangle r baseP old q))
    (inner-square : (new-inner ∙ (π ◁ edge)) =₂
      (inner ∙ restrict-triangle π u old-inner q)) where
    private
      old-post = post-triangle π r baseP old
      new-post = post-triangle π r baseT new
      tail = ((π ∘ r) ◁ δ) ∙ comp-assoc q baseP (π ∘ r)
      A′ = comp-assoc q u π
      coordinate = post-triangle-change π r baseP q baseT δ old new edge outer-square
      projection = unrestrict-square π u q v edge old-inner new-inner inner inner-square

    image : ((new-inner ∙ new-post) ∙ tail) =₂ ((inner ∙ ((old-inner ∙ old-post) ▷ q)))
    image = comp₌-cong (id₌ inner) ((preWhisker-comp₌ old-inner old-post q) ⁻¹) ∙
      (comp₌-assoc inner (old-inner ▷ q) (old-post ▷ q) ∙
        (comp₌-cong projection (id₌ (old-post ▷ q)) ∙
          ((comp₌-assoc new-inner ((π ◁ edge) ∙ A′) (old-post ▷ q)) ⁻¹ ∙
            (comp₌-cong (id₌ new-inner) ((comp₌-assoc (π ◁ edge) A′ (old-post ▷ q)) ⁻¹) ∙
              (comp₌-cong (id₌ new-inner) coordinate ∙
                comp₌-assoc new-inner new-post tail)))))

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


module TripleEvaluationOuterImage {Γ : Context} {P T C : CAT Γ}
  (s m t : MAP P C) (q : MAP T P) (x y z : MAP T C)
  (first-frame : (s ∘ q) =₁ x) (middle-frame : (m ∘ q) =₁ y)
  (last-frame : (t ∘ q) =₁ z) where
  private
    baseP : MAP P ((C × C) × C)
    baseP = pair (pair s m) t
    baseT : MAP T ((C × C) × C)
    baseT = pair (pair x y) z
    k : MAP ((C × C) × C) (C × C)
    k = pair (pr₁ ∘ pr₁) pr₂
    first-pair : (pair s m ∘ q) =₁ pair x y
    first-pair = pair⁼ first-frame middle-frame ∙ pair-pre s m q
    base-cell : (baseP ∘ q) =₁ baseT
    base-cell = pair⁼ first-pair last-frame ∙ pair-pre (pair s m) t q
    module Old = Triple s m t
    module New = Triple x y z
    old-first = pair-β₁ (pair s m) t
    new-first = pair-β₁ (pair x y) z
    outer-first = pair-evaluation-over₁-One (pair s m) t q first-pair last-frame
    outer-last = pair-evaluation-over₂-One (pair s m) t q first-pair last-frame
    module First = NestedVertexImage pr₁ baseP q baseT base-cell pr₁
      old-first new-first first-pair (pair-β₁ s m) (pair-β₁ x y) first-frame
      outer-first (pair-evaluation-over₁-One s m q first-frame middle-frame)
    last-base-square = unrestrict-square pr₂ baseP q baseT base-cell
      Old.third New.third last-frame outer-last
    module Outer = PairedBaseImage (pr₁ ∘ pr₁) pr₂ baseP q baseT base-cell
      Old.first Old.third New.first New.third first-frame last-frame
      First.image last-base-square

  before : (k ∘ baseP) =₁ pair s t
  before = pair⁼ Old.first Old.third ∙ pair-pre (pr₁ ∘ pr₁) pr₂ baseP

  after : (k ∘ baseT) =₁ pair x z
  after = pair⁼ New.first New.third ∙ pair-pre (pr₁ ∘ pr₁) pr₂ baseT

  outer-frame : ((pair s t) ∘ q) =₁ pair x z
  outer-frame = pair⁼ first-frame last-frame ∙ pair-pre s t q

  image : (after ∙ ((k ◁ base-cell) ∙ comp-assoc q baseP k)) =₂
    (outer-frame ∙ (before ▷ q))
  image = Outer.image
```
