# Evaluation along a specified section

A triangle `b : pi ∘ i = id` evaluates a functor pulled back along `pi`
by restricting it to `i`. Evaluation respects restriction and
postcomposition, and retains a supplied comparison with a pulled-back
functor. These laws use the specified triangle throughout.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-triangle; restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-comp; post-restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (right-unitor-comp; triangle-whiskered; whisker-mixed-One)

module SectionEvaluation {Γ : Context} {X K : CAT Γ}
  (pi : MAP K X) (i : MAP X K) (b : (pi ∘ i) =₁ id X) where

  image : {Y : CAT Γ} (h : MAP X Y) → ((h ∘ pi) ∘ i) =₁ h
  image h = comp-unitʳ h ∙ post-triangle h pi i b

  module Restriction {R Y : CAT Γ} (r : MAP R X) (h : MAP X Y) where
    private
      inner = post-triangle h pi i b
      base-cell = comp-unitˡ r ∙ restrict-triangle pi i b r
      after = comp-assoc (i ∘ r) pi h
      outer = comp-assoc r i (h ∘ pi)
      middle = comp-assoc r (id X) h
      given = post-restrict-triangle h pi i r b (comp-unitˡ r)
      normal : (post-triangle h pi (i ∘ r) base-cell ∙ outer) =₂ (image h ▷ r)
      normal = (preWhisker-comp₌ (comp-unitʳ h) inner r) ⁻¹ ∙
        (comp₌-cong ((triangle-whiskered r h) ⁻¹) (id₌ (inner ▷ r)) ∙
          (((comp₌-assoc (h ◁ comp-unitˡ r) middle (inner ▷ r)) ⁻¹) ∙
            (given ∙ comp₌-assoc (h ◁ base-cell) after outer)))

    compatibility :
      ((image h ▷ r) ∙ (comp-assoc r i (h ∘ pi)) ⁻¹) =₂
      post-triangle h pi (i ∘ r) (comp-unitˡ r ∙ restrict-triangle pi i b r)
    compatibility = comp-inv-right (post-triangle h pi (i ∘ r) base-cell) outer ∙
      comp₌-cong (normal ⁻¹) (id₌ (outer ⁻¹))

  postcompose : {Y Z : CAT Γ} (h : MAP X Y) (k : MAP Y Z)
    → image (k ∘ h) =₂
      (post-triangle k (h ∘ pi) i (image h) ∙ (comp-assoc pi h k ▷ i))
  postcompose h k =
    let B = post-triangle h pi i b
        A = comp-assoc i (h ∘ pi) k
        tail = comp-assoc pi h k ▷ i
        unit-image = k ◁ comp-unitʳ h
        triangle-image = k ◁ B
        first = comp₌-cong (right-unitor-comp h k)
          (id₌ (post-triangle (k ∘ h) pi i b))
        second = comp₌-assoc unit-image (comp-assoc (id X) h k)
          (post-triangle (k ∘ h) pi i b)
        third = comp₌-cong (id₌ unit-image) (post-triangle-comp k h pi i b)
        fourth = (comp₌-assoc unit-image triangle-image (A ∙ tail)) ⁻¹
        fifth = comp₌-cong ((postWhisker-comp₌ k (comp-unitʳ h) B) ⁻¹) (id₌ (A ∙ tail))
        sixth = (comp₌-assoc (k ◁ image h) A tail) ⁻¹
    in sixth ∙ (fifth ∙ (fourth ∙ (third ∙ (second ∙ first))))

  module Compared {Y Z : CAT Γ} (h : MAP X Y) (q : MAP K Y)
    (eta : q =₁ (h ∘ pi)) (k : MAP Y Z) where
    comparison : (k ∘ q) =₁ ((k ∘ h) ∘ pi)
    comparison = (comp-assoc pi h k) ⁻¹ ∙ (k ◁ eta)

    private
      S = image h
      A = comp-assoc pi h k ▷ i
      B = (k ◁ eta) ▷ i
      input-frame = comp-assoc i (h ∘ pi) k
      output-frame = comp-assoc i q k
      F = k ◁ S
      restricted : (comparison ▷ i) =₂ ((A ⁻¹) ∙ B)
      restricted = comp₌-cong (preWhisker-inverse (comp-assoc pi h k) i) (id₌ B) ∙
        preWhisker-comp₌ ((comp-assoc pi h k) ⁻¹) (k ◁ eta) i
      cancel : (((F ∙ input-frame) ∙ A) ∙ ((A ⁻¹) ∙ B)) =₂ ((F ∙ input-frame) ∙ B)
      cancel = comp₌-cong (id₌ (F ∙ input-frame)) (comp-inv-left A B) ∙
        comp₌-assoc (F ∙ input-frame) A ((A ⁻¹) ∙ B)

    compatibility :
      (image (k ∘ h) ∙ (comparison ▷ i)) =₂
      ((k ◁ (image h ∙ (eta ▷ i))) ∙ comp-assoc i q k)
    compatibility = comp₌-cong ((postWhisker-comp₌ k S (eta ▷ i)) ⁻¹) (id₌ output-frame) ∙
      (((comp₌-assoc F (k ◁ (eta ▷ i)) output-frame) ⁻¹) ∙
        (comp₌-cong (id₌ F) (whisker-mixed-One eta i k) ∙
          (comp₌-assoc F input-frame B ∙
            (cancel ∙ comp₌-cong (postcompose h k) restricted))))
```


Evaluation along a specified section also respects pairing. A supplied
comparison into the pulled-back pair retains its two coordinate images.

```agda
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-pre-id; pair-pre-iterated; pair-pre-natural-inputs-One; pair-pre-natural-substitution-One)

module SectionPairing {Γ : Context} {X K A B : CAT Γ}
  (pi : MAP K X) (i : MAP X K) (b : (pi ∘ i) =₁ id X)
  (u : MAP X A) (v : MAP X B) where
  module E = SectionEvaluation pi i b
  private
    j = pair u v
    ru = comp-unitʳ u
    rv = comp-unitʳ v
    units = pair⁼ ru rv
    inputs = pair⁼ (u ◁ b) (v ◁ b)
    au = comp-assoc i pi u
    av = comp-assoc i pi v
    associator = comp-assoc i pi j
    associators = pair⁼ au av
    before = pair-pre u v (pi ∘ i)
    after = pair-pre u v (id X)
    inner = pair-pre (u ∘ pi) (v ∘ pi) i
    outer = pair-pre u v pi ▷ i
    coordinates = pair⁼ (E.image u) (E.image v)
    expand-unit = comp₌-assoc units after ((j ◁ b) ∙ associator) ∙
      comp₌-cong ((pair-pre-id u v) ⁻¹) (id₌ ((j ◁ b) ∙ associator))
    change-input = comp₌-cong (id₌ units)
      (comp₌-assoc inputs before associator ∙
        (comp₌-cong (pair-pre-natural-substitution-One u v b) (id₌ associator) ∙
          ((comp₌-assoc after (j ◁ b) associator) ⁻¹)))
    compose-inputs = comp₌-cong (id₌ units)
      (comp₌-cong (id₌ inputs) (pair-pre-iterated u v pi i))
    collect-coordinates = (pair⁼-comp ru ((u ◁ b) ∙ au) rv ((v ◁ b) ∙ av)) ⁻¹ ∙
      comp₌-cong (id₌ units) ((pair⁼-comp (u ◁ b) au (v ◁ b) av) ⁻¹)
    finish = comp₌-cong collect-coordinates (id₌ (inner ∙ outer)) ∙
      (((comp₌-assoc units (inputs ∙ associators) (inner ∙ outer)) ⁻¹) ∙
        comp₌-cong (id₌ units) ((comp₌-assoc inputs associators (inner ∙ outer)) ⁻¹))

  compatibility : E.image (pair u v) =₂
    (pair⁼ (E.image u) (E.image v) ∙
      (pair-pre (u ∘ pi) (v ∘ pi) i ∙ (pair-pre u v pi ▷ i)))
  compatibility = finish ∙ (compose-inputs ∙ (change-input ∙ expand-unit))

  module Compared {f : MAP K A} {g : MAP K B}
    (alpha : f =₁ (u ∘ pi)) (beta : g =₁ (v ∘ pi)) where
    input = pair⁼ alpha beta
    comparison = (pair-pre u v pi) ⁻¹ ∙ input
    private
      pair-before = pair-pre u v pi
      pair-after = pair-pre (u ∘ pi) (v ∘ pi) i
      input-image = input ▷ i
      step = pair-pre f g i
      cu = E.image u
      cv = E.image v
      changed = pair⁼ (alpha ▷ i) (beta ▷ i)
      restricted : (comparison ▷ i) =₂ (((pair-before ▷ i) ⁻¹) ∙ input-image)
      restricted = comp₌-cong (preWhisker-inverse pair-before i) (id₌ input-image) ∙
        preWhisker-comp₌ (pair-before ⁻¹) input i
      cancel-comparison = comp₌-cong (id₌ coordinates)
          (comp₌-cong (id₌ pair-after) (comp-inv-left (pair-before ▷ i) input-image) ∙
            comp₌-assoc pair-after (pair-before ▷ i) (((pair-before ▷ i) ⁻¹) ∙ input-image)) ∙
        comp₌-assoc coordinates (pair-after ∙ (pair-before ▷ i))
          (((pair-before ▷ i) ⁻¹) ∙ input-image)

    evaluation : (E.image (pair u v) ∙ (comparison ▷ i)) =₂
      (pair⁼ (cu ∙ (alpha ▷ i)) (cv ∙ (beta ▷ i)) ∙ pair-pre f g i)
    evaluation = comp₌-cong ((pair⁼-comp cu (alpha ▷ i) cv (beta ▷ i)) ⁻¹) (id₌ step) ∙
      (((comp₌-assoc coordinates changed step) ⁻¹) ∙
        (comp₌-cong (id₌ coordinates) (pair-pre-natural-inputs-One alpha beta i) ∙
          (cancel-comparison ∙ comp₌-cong compatibility restricted)))
```
