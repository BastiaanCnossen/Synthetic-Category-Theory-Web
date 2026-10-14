# Family naturality of beta-first composition evaluation

This module proves naturality for the selected literal beta-first comparison. The family parameter is
independent of the term source, and neither needs an anima hypothesis.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CompositionEvaluationFamily where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-assoc; preWhisker-id₌; postWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (postWhisker-id; postWhisker-comp)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼; pair-pre)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-square-cell; post-square-cell-inner; post-triangle-inner)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction using (uncurry-restrict-substitution)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying using (uncurry⁼; uncurry⁼-evaluate)
open import SCT.VolumeI.Chapter01.Section04.Composition using (compose⁼; doubleEvaluation; mapComp; mapComp-β)
open import SCT.VolumeI.Chapter01.Section04.CompositionEvaluation using (module CompositionCoordinates; composition-evaluation)

module _ {Γ : Context} {X : CAT Γ} where
  open Terms.Equalities X using (_＝_)

  module FamilyCoordinates {P C D E : CAT Γ}
    {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
    (α : g ＝ g′) (β : f ＝ f′) where
    module Before = CompositionCoordinates g f
      using (K; input; inner-input; outer-input; evaluated-inner; outer-map; first; second; third;
        inner-coordinate; inner-evaluation; left-normalization; right-normalization; comparison; evaluation)
    module After = CompositionCoordinates g′ f′
      using (input; inner-input; evaluated-inner; outer-map; first; second; third;
        inner-coordinate; inner-evaluation; left-normalization; right-normalization; comparison; evaluation)

    private
      second-input : MAP (P × C) C
      second-input = pr₂

      fixed-C : (id C) ＝ (id C)
      fixed-C = const {P = X} (id₌ (id C))

      fixed-input : (id C ∘ second-input) ＝ (id C ∘ second-input)
      fixed-input = const {P = X} (id₌ (id C ∘ second-input))

    paired = pair⁼ α β
    input-action = productMap-cong paired fixed-C
    inner-action = productMap-cong β fixed-C
    inner-evaluation-action = pair⁼ (const (id₌ pr₁)) (uncurry⁼ β)
    outer-action = productMap-cong α (const (id₌ (id D)))
    common-action = pair⁼ (α ▷ pr₁) (uncurry⁼ β)

    private
      input-first = productMap-cong-triangle₁ paired (const (id₌ (id C)))

      module Nested {A : CAT Γ} (π : MAP Before.K A) {z z′ : MAP P A}
        (b : (π ∘ pair g f) =₁ z) (b′ : (π ∘ pair g′ f′) =₁ z′)
        (change : z ＝ z′)
        (projection : SquareCell₌ (π ◁ paired) change (const b) (const b′)) where
        before = post-square-cell π (pr₁ {C = P} {D = C}) (pair g f)
          (pr₁ {C = Before.K} {D = C}) Before.input
          (pair-β₁ ((pair g f) ∘ pr₁) (id C ∘ pr₂))
        after = post-square-cell π (pr₁ {C = P} {D = C}) (pair g′ f′)
          (pr₁ {C = Before.K} {D = C}) After.input
          (pair-β₁ ((pair g′ f′) ∘ pr₁) (id C ∘ pr₂))

        square : SquareCell₌ ((π ∘ pr₁) ◁ input-action) (change ▷ pr₁)
          (const ((b ▷ pr₁) ∙ before)) (const ((b′ ▷ pr₁) ∙ after))
        square =
          let coordinate = post-square-cell-inner (pr₁ {C = P} {D = C})
                (pr₁ {C = Before.K} {D = C}) π
                (pair-β₁ ((pair g f) ∘ pr₁) (id C ∘ pr₂))
                (pair-β₁ ((pair g′ f′) ∘ pr₁) (id C ∘ pr₂))
                paired input-action input-first
              beta = replace-sides₌ (pre-constant b pr₁) (pre-constant b′ pr₁)
                (pre-square₌ pr₁ projection)
          in replace-sides₌ (const-comp (b ▷ pr₁) before)
            (const-comp (b′ ▷ pr₁) after) (paste-square₌ coordinate beta)

      module First = Nested pr₁ (pair-β₁ g f) (pair-β₁ g′ f′) α
        (pair⁼-triangle₁ α β)
      module Second = Nested pr₂ (pair-β₂ g f) (pair-β₂ g′ f′) β
        (pair⁼-triangle₂ α β)

    first-square : SquareCell₌ ((pr₁ ∘ pr₁) ◁ input-action) (α ▷ pr₁)
      (const Before.first) (const After.first)
    first-square = First.square

    second-square : SquareCell₌ ((pr₂ ∘ pr₁) ◁ input-action) (β ▷ pr₁)
      (const Before.second) (const After.second)
    second-square = Second.square

    private
      identity-coordinate : (fixed-C ▷ second-input) =₁ fixed-input
      identity-coordinate = const-cong (preWhisker-id₌ (id C) second-input) ∙
        pre-constant (id₌ (id C)) second-input

    third-square : SquareCell₌ (pr₂ ◁ input-action) fixed-input
      (const Before.third) (const After.third)
    third-square = replace-edges₌ (id₌ _) identity-coordinate
      (productMap-cong-triangle₂ paired fixed-C)

    inner-coordinate-square : SquareCell₌ (Before.inner-input ◁ input-action) inner-action
      (const Before.inner-coordinate) (const After.inner-coordinate)
    inner-coordinate-square =
      let square = pair-evaluation-natural (pr₂ ∘ pr₁) pr₂ input-action
            (const Before.second) (const After.second)
            (const Before.third) (const After.third)
            (β ▷ pr₁) fixed-input second-square third-square
          edge = pair⁼-cong (id₌ (β ▷ pr₁)) (identity-coordinate ⁻¹)
          before = (const-comp (pair⁼ Before.second Before.third)
              (pair-pre (pr₂ ∘ pr₁) pr₂ Before.input)) ∙
            comp₌-cong (pair⁼-constant Before.second Before.third) (id₌ _)
          after = (const-comp (pair⁼ After.second After.third)
              (pair-pre (pr₂ ∘ pr₁) pr₂ After.input)) ∙
            comp₌-cong (pair⁼-constant After.second After.third) (id₌ _)
      in replace-sides₌ before after (replace-edges₌ (id₌ _) edge square)

    inner-evaluation-square : SquareCell₌
      ((mapEval ∘ Before.inner-input) ◁ input-action) (uncurry⁼ β)
      (const Before.inner-evaluation) (const After.inner-evaluation)
    inner-evaluation-square = replace-edges₌ (id₌ _) ((uncurry⁼-evaluate β) ⁻¹)
      (post-triangle-inner mapEval Before.inner-input input-action inner-action
        Before.inner-coordinate After.inner-coordinate inner-coordinate-square)

    left-normalization-square : SquareCell₌ (Before.outer-input ◁ input-action) common-action
      (const Before.left-normalization) (const After.left-normalization)
    left-normalization-square =
      let square = pair-evaluation-natural (pr₁ ∘ pr₁) (mapEval ∘ Before.inner-input) input-action
            (const Before.first) (const After.first)
            (const Before.inner-evaluation) (const After.inner-evaluation)
            (α ▷ pr₁) (uncurry⁼ β) first-square inner-evaluation-square
          before = (const-comp (pair⁼ Before.first Before.inner-evaluation)
              (pair-pre (pr₁ ∘ pr₁) (mapEval ∘ Before.inner-input) Before.input)) ∙
            comp₌-cong (pair⁼-constant Before.first Before.inner-evaluation) (id₌ _)
          after = (const-comp (pair⁼ After.first After.inner-evaluation)
              (pair-pre (pr₁ ∘ pr₁) (mapEval ∘ After.inner-input) After.input)) ∙
            comp₌-cong (pair⁼-constant After.first After.inner-evaluation) (id₌ _)
      in replace-sides₌ before after square

    right-normalization-square : SquareCell₌ (outer-action ⋆ inner-evaluation-action) common-action
      (const Before.right-normalization) (const After.right-normalization)
    right-normalization-square =
      let vf = uncurry f
          vf′ = uncurry f′
          bf = uncurry⁼ β
          a = α ▷ pr₁
          cb = const (id₌ (g ∘ pr₁))
          ca = const (id₌ (id D ∘ vf′))
          eb = id D ◁ bf
          inner = productMap-pair-inner g (id D) (const (id₌ pr₁)) bf
          outer = productMap-pair-outer α (const (id₌ (id D))) pr₁ vf′
          first-identity = const-cong (postWhisker-id₌ g pr₁) ∙ post-constant g (id₌ pr₁)
          second-identity = const-cong (preWhisker-id₌ (id D) vf′) ∙ pre-constant (id₌ (id D)) vf′
          raw-normalize = pair⁼-cong (comp₌-unitʳ a) (comp₌-unitˡ eb) ∙
            (((pair⁼-comp a cb ca eb) ⁻¹) ∙
              comp₌-cong (pair⁼-cong (id₌ a) second-identity)
                (pair⁼-cong first-identity (id₌ eb)))
          base-square = replace-edges₌ (id₌ _) raw-normalize (adjoin-square₌ inner outer)
          finish-square = replace-sides₌
            (pair⁼-constant (id₌ (g ∘ pr₁)) (comp-unitˡ vf))
            (pair⁼-constant (id₌ (g′ ∘ pr₁)) (comp-unitˡ vf′))
            (pair⁼-square (identity-square₌ a) (postWhisker-id bf))
      in replace-sides₌
        (const-comp (pair⁼ (id₌ (g ∘ pr₁)) (comp-unitˡ vf))
          (productMap-pair g (id D) pr₁ vf))
        (const-comp (pair⁼ (id₌ (g′ ∘ pr₁)) (comp-unitˡ vf′))
          (productMap-pair g′ (id D) pr₁ vf′))
        (paste-square₌ base-square finish-square)

    comparison-square : SquareCell₌ (Before.outer-input ◁ input-action)
      (outer-action ⋆ inner-evaluation-action)
      (const Before.comparison) (const After.comparison)
    comparison-square =
      let before = const-comp (Before.right-normalization ⁻¹) Before.left-normalization ∙
            comp₌-cong ((const-inv Before.right-normalization) ⁻¹) (id₌ _)
          after = const-comp (After.right-normalization ⁻¹) After.left-normalization ∙
            comp₌-cong ((const-inv After.right-normalization) ⁻¹) (id₌ _)
      in replace-sides₌ before after
        (transpose-square₌ (inv-comp-square₌ (transpose-square₌ left-normalization-square)
          (transpose-square₌ right-normalization-square)))

    private
      paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
        {t : x ＝ y} {m : x′ ＝ y′} {b : x″ ＝ y″}
        {l₁ : x =₁ x′} {r₁ : y =₁ y′} {l₂ : x′ =₁ x″} {r₂ : y′ =₁ y″}
        → SquareCell₌ t m (const l₁) (const r₁)
        → SquareCell₌ m b (const l₂) (const r₂)
        → SquareCell₌ t b (const (l₂ ∙ l₁)) (const (r₂ ∙ r₁))
      paste-fixed {l₁ = l₁} {r₁ = r₁} {l₂ = l₂} {r₂ = r₂} first second =
        replace-sides₌ (const-comp l₂ l₁) (const-comp r₂ r₁) (paste-square₌ first second)

      inverse-fixed : {A B : CAT Γ} {x y x′ y′ : MAP A B}
        {t : x ＝ y} {b : x′ ＝ y′} {l : x =₁ x′} {r : y =₁ y′}
        → SquareCell₌ t b (const l) (const r)
        → SquareCell₌ b t (const (l ⁻¹)) (const (r ⁻¹))
      inverse-fixed {l = l} {r = r} square =
        replace-sides₌ ((const-inv l) ⁻¹) ((const-inv r) ⁻¹) (inverse-square₌ square)

      target-frame : SquareCell₌
        ((mapEval ◁ outer-action) ⋆ inner-evaluation-action)
        (mapEval ◁ (outer-action ⋆ inner-evaluation-action))
        (const (comp-assoc Before.evaluated-inner Before.outer-map mapEval))
        (const (comp-assoc After.evaluated-inner After.outer-map mapEval))
      target-frame = replace-edges₌
        (hcomp-cong (hcomp-id-outer mapEval outer-action) (id₌ inner-evaluation-action))
        (hcomp-id-outer mapEval (outer-action ⋆ inner-evaluation-action))
        (assoc-natural (const (id₌ mapEval)) outer-action inner-evaluation-action)

    coordinate-evaluation-square : SquareCell₌ (doubleEvaluation ◁ input-action)
      (uncurry⁼ α ⋆ inner-evaluation-action)
      (const Before.evaluation) (const After.evaluation)
    coordinate-evaluation-square =
      let source-frame = postWhisker-comp input-action Before.outer-input mapEval
          posted = replace-sides₌
            (post-constant mapEval Before.comparison) (post-constant mapEval After.comparison)
            (post-square₌ mapEval comparison-square)
          target-action = hcomp-cong ((uncurry⁼-evaluate α) ⁻¹) (id₌ inner-evaluation-action)
      in replace-edges₌ (id₌ _) target-action
        (paste-fixed (paste-fixed source-frame posted) (inverse-fixed target-frame))

    composition-evaluation-natural : SquareCell₌ (uncurry⁼ (compose⁼ α β))
      (uncurry⁼ α ⋆ inner-evaluation-action)
      (const (composition-evaluation g f)) (const (composition-evaluation g′ f′))
    composition-evaluation-natural =
      let source = uncurry-restrict-substitution mapComp paired
          fixed-beta = interchange-fixedOuter mapComp-β input-action
      in paste-fixed (paste-fixed source fixed-beta) coordinate-evaluation-square
```