# Direct evaluation of composition

The selected composition comparison is constructed directly from the
representing beta and product coordinates. Its native restriction, family
naturality and full relative restriction have been checked. EvaluationOverBase
selects this constructor; the actual default-law comparisons remain separate
obligations.

`CompositionCoordinates` gives the constructor. `CompositionRestriction`
first compares its two coordinate normalizations, then transports the resulting
quotient through evaluation. The final native restriction theorem also pastes
the representing beta and the source composition comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CompositionEvaluation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; comp-unitˡ; postWhisker-id₌; preWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (adjoin-square₌; replace-edges₌; replace-sides₌; transpose-square₌; unconst-sides₌; paste-square₌; identity-square₌; inv-comp-square₌; inverse-square₌)
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (postWhisker-id)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (unrestrict-square; restrict-triangle; post-square-cell-inner; post-square-cell-outer; post-square-cell; post-square-cell-comp; post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-inverse; post-triangle-change)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (whisker-mixed-One)
import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams as Restriction
open Restriction using (RestrictionDiagram; restriction-diagram; Evaluation; Compatible-One; post-compatible)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair; productMap-pair-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong; productMap-cong₂; productMap-cong-triangle₁; productMap-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-pre-over₁-One; pair-pre-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One; comp₌-inverseʳ-One; inverse-unique; inverse-inverse; inverse-composite; postWhisker-inverse; preWhisker-inverse; cancel-left)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-cong; pair⁼-id-One; pair⁼-square; pair⁼-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares using (pair-evaluations-One; pair-compatible-One)
import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution as FirstFactor
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying using (uncurry-restrict; uncurry⁼; uncurry⁼-composition)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport using (identification-restriction)
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction
  using (uncurry-restrict-iterated; uncurry-restrict-substitution; module EvaluationChange)
open import SCT.VolumeI.Chapter01.Section04.Composition using (compose; compose-pre; doubleEvaluation; mapComp; mapComp-β)

module _ {Γ : Context} where
  module CompositionCoordinates {P C D E : CAT Γ} (g : MAP P (Map D E)) (f : MAP P (Map C D)) where
    K : CAT Γ
    K = Map D E × Map C D

    input : MAP (P × C) (K × C)
    input = productMap (pair g f) (id C)

    inner-input : MAP (K × C) (Map C D × C)
    inner-input = pair (pr₂ ∘ pr₁) pr₂

    outer-input : MAP (K × C) (Map D E × D)
    outer-input = pair (pr₁ ∘ pr₁) (mapEval ∘ inner-input)

    evaluated-inner : MAP (P × C) (P × D)
    evaluated-inner = pair pr₁ (uncurry f)

    outer-map : MAP (P × D) (Map D E × D)
    outer-map = productMap g (id D)

    first : ((pr₁ ∘ pr₁) ∘ input) =₁ (g ∘ pr₁)
    first = (pair-β₁ g f ▷ pr₁) ∙
      ((comp-assoc pr₁ (pair g f) pr₁) ⁻¹ ∙
        ((pr₁ ◁ pair-β₁ ((pair g f) ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc input pr₁ pr₁))

    second : ((pr₂ ∘ pr₁) ∘ input) =₁ (f ∘ pr₁)
    second = (pair-β₂ g f ▷ pr₁) ∙
      ((comp-assoc pr₁ (pair g f) pr₂) ⁻¹ ∙
        ((pr₂ ◁ pair-β₁ ((pair g f) ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc input pr₁ pr₂))

    third : (pr₂ ∘ input) =₁ (id C ∘ pr₂)
    third = pair-β₂ ((pair g f) ∘ pr₁) (id C ∘ pr₂)

    inner-coordinate : (inner-input ∘ input) =₁ productMap f (id C)
    inner-coordinate = pair⁼ second third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ input

    inner-evaluation : ((mapEval ∘ inner-input) ∘ input) =₁ uncurry f
    inner-evaluation = (mapEval ◁ inner-coordinate) ∙ comp-assoc input inner-input mapEval

    left-normalization : (outer-input ∘ input) =₁ pair (g ∘ pr₁) (uncurry f)
    left-normalization = pair⁼ first inner-evaluation ∙
      pair-pre (pr₁ ∘ pr₁) (mapEval ∘ inner-input) input

    right-normalization : (outer-map ∘ evaluated-inner) =₁ pair (g ∘ pr₁) (uncurry f)
    right-normalization = pair⁼ (id₌ (g ∘ pr₁)) (comp-unitˡ (uncurry f)) ∙
      productMap-pair g (id D) pr₁ (uncurry f)

    comparison : (outer-input ∘ input) =₁ (outer-map ∘ evaluated-inner)
    comparison = right-normalization ⁻¹ ∙ left-normalization

    evaluation : (doubleEvaluation ∘ input) =₁ (uncurry g ∘ evaluated-inner)
    evaluation = (comp-assoc evaluated-inner outer-map mapEval) ⁻¹ ∙
      ((mapEval ◁ comparison) ∙ comp-assoc input outer-input mapEval)

  composition-evaluation : {P C D E : CAT Γ}
    (g : MAP P (Map D E)) (f : MAP P (Map C D))
    → uncurry (compose g f) =₁ (uncurry g ∘ pair pr₁ (uncurry f))
  composition-evaluation g f = CompositionCoordinates.evaluation g f ∙
    ((mapComp-β ▷ CompositionCoordinates.input g f) ∙ uncurry-restrict mapComp (pair g f))
```

The restriction boundaries below are specified independently of the
comparison. Both coordinate normalizations commute with these boundaries.
The parameter change retains its actual common-coordinate routes, without
importing downstream composition coherence.

```agda
module _ {Γ : Context} where
  module CompositionRestriction {P Q C D E : CAT Γ}
    (r : MAP Q P) (g : MAP P (Map D E)) (f : MAP P (Map C D)) where
    module Before = CompositionCoordinates g f
      using (K; input; inner-input; outer-input; evaluated-inner; outer-map; first; second; third;
        inner-coordinate; inner-evaluation; left-normalization; right-normalization; comparison; evaluation)
    module After = CompositionCoordinates (g ∘ r) (f ∘ r)
      using (input; inner-input; outer-input; evaluated-inner; outer-map; first; second; third;
        inner-coordinate; inner-evaluation; left-normalization; right-normalization; comparison; evaluation)

    sC : MAP (Q × C) (P × C)
    sC = productMap r (id C)
    sD : MAP (Q × D) (P × D)
    sD = productMap r (id D)

    input-change : (Before.input ∘ sC) =₁ After.input
    input-change = productMap-cong (pair-pre g f r) (id₌ (id C)) ∙
      productMap-first-comp (pair g f) r

    left-change : ((Before.outer-input ∘ Before.input) ∘ sC) =₁
      (After.outer-input ∘ After.input)
    left-change = (Before.outer-input ◁ input-change) ∙
      comp-assoc sC Before.input Before.outer-input

    private
      module RawEvaluation = EvaluationChange {C = C} {D = D} r
        using (common; input-route; output-route; comparison)

      common : MAP (Q × C) (P × D)
      common = RawEvaluation.common f

      evaluation-input : (sD ∘ After.evaluated-inner) =₁ common
      evaluation-input = RawEvaluation.input-route f

      evaluation-output : (Before.evaluated-inner ∘ sC) =₁ common
      evaluation-output = RawEvaluation.output-route f

    evaluation-change : (sD ∘ After.evaluated-inner) =₁ (Before.evaluated-inner ∘ sC)
    evaluation-change = RawEvaluation.comparison f

    outer-change : (Before.outer-map ∘ sD) =₁ After.outer-map
    outer-change = productMap-first-comp g r

    right-change : ((Before.outer-map ∘ Before.evaluated-inner) ∘ sC) =₁
      (After.outer-map ∘ After.evaluated-inner)
    right-change = (outer-change ▷ After.evaluated-inner) ∙
      ((comp-assoc After.evaluated-inner sD Before.outer-map) ⁻¹ ∙
        ((Before.outer-map ◁ evaluation-change ⁻¹) ∙
          comp-assoc sC Before.evaluated-inner Before.outer-map))

    common-change : (pair (g ∘ pr₁) (uncurry f) ∘ sC) =₁
      pair ((g ∘ r) ∘ pr₁) (uncurry (f ∘ r))
    common-change = pair⁼ (FirstFactor.Coordinates.first C g r)
      ((uncurry-restrict f r) ⁻¹) ∙ pair-pre (g ∘ pr₁) (uncurry f) sC

    private
      module InputCoordinates = FirstFactor.Coordinates C (pair g f) r
        using (first; second; projection₁; projection₂)
      input-action = productMap-cong (pair-pre g f r) (id₌ (id C))

      input-first-coordinate = (pair-pre g f r ▷ pr₁) ∙ InputCoordinates.first
      input-second-coordinate = (id₌ (id C) ▷ pr₂) ∙ InputCoordinates.second

      opaque
        input-first : SquareCell₌ (pr₁ ◁ input-change) input-first-coordinate
          (project-pair₁ ((pair g f) ∘ pr₁) (id C ∘ pr₂) sC)
          (pair-β₁ ((pair (g ∘ r) (f ∘ r)) ∘ pr₁) (id C ∘ pr₂))
        input-first = replace-edges₌
          ((postWhisker-comp₌ pr₁ input-action (productMap-first-comp (pair g f) r)) ⁻¹)
          (id₌ input-first-coordinate)
          (adjoin-square₌ InputCoordinates.projection₁
            (unconst-sides₌ (productMap-cong-triangle₁ (pair-pre g f r) (id₌ (id C)))))

      opaque
        input-second : SquareCell₌ (pr₂ ◁ input-change) input-second-coordinate
          (project-pair₂ ((pair g f) ∘ pr₁) (id C ∘ pr₂) sC)
          (pair-β₂ ((pair (g ∘ r) (f ∘ r)) ∘ pr₁) (id C ∘ pr₂))
        input-second = replace-edges₌
          ((postWhisker-comp₌ pr₂ input-action (productMap-first-comp (pair g f) r)) ⁻¹)
          (id₌ input-second-coordinate)
          (adjoin-square₌ InputCoordinates.projection₂
            (unconst-sides₌ (productMap-cong-triangle₂ (pair-pre g f r) (id₌ (id C)))))


      input-diagram : RestrictionDiagram {E = One} {Q = Q × C} (P × C) (Before.K × C)
      input-diagram = restriction-diagram Before.input sC After.input input-change

      third-evaluation : Evaluation input-diagram pr₂ (id C ∘ pr₂)
        (id C ∘ pr₂) (id C ∘ pr₂)
      third-evaluation = Restriction.evaluation After.third Before.third InputCoordinates.second (id₌ (id C) ▷ pr₂)

      opaque
        third-compatible : Compatible-One input-diagram third-evaluation
        third-compatible = comp₌-assoc (id₌ (id C) ▷ pr₂) InputCoordinates.second (Before.third ▷ sC) ∙
          unrestrict-square pr₂ Before.input sC After.input input-change
            Before.third After.third input-second-coordinate input-second


      module NestedCoordinate {A : CAT Γ} (π : MAP Before.K A) (v : MAP P A)
        (bP : (π ∘ pair g f) =₁ v)
        (bQ : (π ∘ pair (g ∘ r) (f ∘ r)) =₁ (v ∘ r))
        (beta-restrict : (bQ ∙ ((π ◁ pair-pre g f r) ∙ comp-assoc r (pair g f) π)) =₂ (bP ▷ r)) where
        h = pair g f
        α = pair-pre g f r
        coordinate-before = FirstFactor.Coordinates.first C π h
        coordinate-middle = FirstFactor.Coordinates.first C π (h ∘ r)
        coordinate-after = FirstFactor.Coordinates.first C π (pair (g ∘ r) (f ∘ r))
        coordinate-source = FirstFactor.Coordinates.first C (π ∘ h) r
        coordinate-target = FirstFactor.Coordinates.first C v r
        corner = comp-assoc r h π
        step = ((π ∘ pr₁) ◁ productMap-first-comp h r) ∙
          comp-assoc sC Before.input (π ∘ pr₁)
        middle = ((π ◁ α) ▷ pr₁) ∙ ((corner ▷ pr₁) ∙ coordinate-source)
        chosen-before = (bP ▷ pr₁) ∙ coordinate-before
        chosen-after = (bQ ▷ pr₁) ∙ coordinate-after

        opaque
          compatible : SquareCell₌ (chosen-before ▷ sC) chosen-after
            (((π ∘ pr₁) ◁ input-change) ∙ comp-assoc sC Before.input (π ∘ pr₁)) coordinate-target
          compatible =
            let first-stage = (comp₌-assoc (corner ▷ pr₁) coordinate-source (coordinate-before ▷ sC)) ⁻¹ ∙
                  FirstFactor.first-coordinate-assoc C π h r
                action-stage = unconst-sides₌
                  (post-square-cell-inner (pr₁ {C = Q} {D = C}) (pr₁ {C = Before.K} {D = C}) π
                    (pair-β₁ ((h ∘ r) ∘ pr₁) (id C ∘ pr₂))
                    (pair-β₁ ((pair (g ∘ r) (f ∘ r)) ∘ pr₁) (id C ∘ pr₂)) α input-action
                    (productMap-cong-triangle₁ α (id₌ (id C))))
                change-normalization =
                  comp₌-assoc ((π ∘ pr₁) ◁ input-action)
                    ((π ∘ pr₁) ◁ productMap-first-comp h r)
                    (comp-assoc sC Before.input (π ∘ pr₁)) ∙
                  comp₌-cong (postWhisker-comp₌ (π ∘ pr₁) input-action (productMap-first-comp h r))
                    (id₌ (comp-assoc sC Before.input (π ∘ pr₁)))
                first-square = replace-sides₌ (change-normalization ⁻¹) (id₌ middle)
                  (transpose-square₌ (adjoin-square₌ first-stage action-stage))
                merge = (preWhisker pr₁ ◁ (beta-restrict ∙ comp₌-assoc bQ (π ◁ α) corner)) ∙
                  ((preWhisker-comp₌ (bQ ∙ (π ◁ α)) corner pr₁) ⁻¹ ∙
                    comp₌-cong ((preWhisker-comp₌ bQ (π ◁ α) pr₁) ⁻¹) (id₌ (corner ▷ pr₁)))
                collapse = comp₌-cong merge (id₌ coordinate-source) ∙
                  ((comp₌-assoc ((bQ ▷ pr₁) ∙ ((π ◁ α) ▷ pr₁)) (corner ▷ pr₁) coordinate-source) ⁻¹ ∙
                    (comp₌-assoc (bQ ▷ pr₁) ((π ◁ α) ▷ pr₁) ((corner ▷ pr₁) ∙ coordinate-source)) ⁻¹)
                beta-square = collapse ⁻¹ ∙ unconst-sides₌
                  (post-square-cell-outer (pr₁ {C = Q} {D = C}) r (pr₁ {C = P} {D = C}) sC
                    (pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)) bP)
            in replace-edges₌ ((preWhisker-comp₌ (bP ▷ pr₁) coordinate-before sC) ⁻¹) (id₌ chosen-after)
              (adjoin-square₌ first-square beta-square)

      first-beta-restrict = comp₌-unitˡ-One (pair-β₁ g f ▷ r) ∙
        unrestrict-square pr₁ (pair g f) r (pair (g ∘ r) (f ∘ r)) (pair-pre g f r)
          (pair-β₁ g f) (pair-β₁ (g ∘ r) (f ∘ r)) (id₌ (g ∘ r)) (pair-pre-over₁-One g f r)

      second-beta-restrict = comp₌-unitˡ-One (pair-β₂ g f ▷ r) ∙
        unrestrict-square pr₂ (pair g f) r (pair (g ∘ r) (f ∘ r)) (pair-pre g f r)
          (pair-β₂ g f) (pair-β₂ (g ∘ r) (f ∘ r)) (id₌ (f ∘ r)) (pair-pre-over₂-One g f r)

      module FirstCoordinate = NestedCoordinate pr₁ g (pair-β₁ g f)
        (pair-β₁ (g ∘ r) (f ∘ r)) first-beta-restrict using (compatible)
      module SecondCoordinate = NestedCoordinate pr₂ f (pair-β₂ g f)
        (pair-β₂ (g ∘ r) (f ∘ r)) second-beta-restrict using (compatible)


      second-evaluation : Evaluation input-diagram (pr₂ ∘ pr₁) (f ∘ pr₁)
        ((f ∘ r) ∘ pr₁) ((f ∘ r) ∘ pr₁)
      second-evaluation = Restriction.evaluation After.second Before.second
        (FirstFactor.Coordinates.first C f r) (id₌ ((f ∘ r) ∘ pr₁))

      opaque
        second-compatible : Compatible-One input-diagram second-evaluation
        second-compatible =
          (comp₌-unitˡ-One (FirstFactor.Coordinates.first C f r ∙ (Before.second ▷ sC))) ⁻¹ ∙
            SecondCoordinate.compatible ⁻¹

      opaque
        inner-coordinate-square : SquareCell₌ (Before.inner-coordinate ▷ sC) After.inner-coordinate
          ((Before.inner-input ◁ input-change) ∙ comp-assoc sC Before.input Before.inner-input)
          (productMap-first-comp f r)
        inner-coordinate-square =
          let finish = pair⁼ (id₌ ((f ∘ r) ∘ pr₁)) (id₌ (id C) ▷ pr₂)
              second = FirstFactor.Coordinates.normalized C f r
              first = Before.inner-coordinate ▷ sC
              finish-normalization = pair⁼-id-One ((f ∘ r) ∘ pr₁) (id C ∘ pr₂) ∙
                pair⁼-cong (id₌ (id₌ ((f ∘ r) ∘ pr₁))) (preWhisker-id₌ (id C) pr₂)
              staged-normalization =
                comp₌-cong ((FirstFactor.Coordinates.normalization C f r) ⁻¹) (id₌ first) ∙
                (comp₌-unitˡ-One (second ∙ first) ∙
                  comp₌-cong finish-normalization (id₌ (second ∙ first)))
          in (staged-normalization ∙
            pair-compatible-One input-diagram second-evaluation third-evaluation second-compatible third-compatible) ⁻¹

      inner-evaluation-data : Evaluation input-diagram Before.inner-input
        (productMap f (id C)) (productMap (f ∘ r) (id C)) (productMap (f ∘ r) (id C))
      inner-evaluation-data = Restriction.evaluation After.inner-coordinate Before.inner-coordinate
        (productMap-first-comp f r) (id₌ (productMap (f ∘ r) (id C)))

      opaque
        inner-evaluation-compatible : Compatible-One input-diagram inner-evaluation-data
        inner-evaluation-compatible =
          (comp₌-unitˡ-One (productMap-first-comp f r ∙ (Before.inner-coordinate ▷ sC))) ⁻¹ ∙
            inner-coordinate-square ⁻¹

      forward-evaluation = post-triangle mapEval (productMap f (id C)) sC (productMap-first-comp f r)

      opaque
        forward-evaluation-normalization : forward-evaluation =₂ ((uncurry-restrict f r) ⁻¹)
        forward-evaluation-normalization =
          (inverse-unique (uncurry-restrict f r) forward-evaluation
            ((const-One (id₌ (uncurry (f ∘ r)))) ⁻¹ ∙
              post-triangle-inverse mapEval (productMap f (id C)) sC (productMap-first-comp f r))) ⁻¹

      opaque
        inner-evaluation-square : SquareCell₌ (Before.inner-evaluation ▷ sC) After.inner-evaluation
          (((mapEval ∘ Before.inner-input) ◁ input-change) ∙
            comp-assoc sC Before.input (mapEval ∘ Before.inner-input))
          ((uncurry-restrict f r) ⁻¹)
        inner-evaluation-square =
          let first = Before.inner-evaluation ▷ sC
              staged-normalization = comp₌-cong forward-evaluation-normalization (id₌ first) ∙
                (comp₌-unitˡ-One (forward-evaluation ∙ first) ∙
                  comp₌-cong (postWhisker-id₌ mapEval (productMap (f ∘ r) (id C)))
                    (id₌ (forward-evaluation ∙ first)))
          in (staged-normalization ∙
            post-compatible input-diagram mapEval inner-evaluation-data inner-evaluation-compatible) ⁻¹

      outer-first-evaluation : Evaluation input-diagram (pr₁ ∘ pr₁) (g ∘ pr₁)
        ((g ∘ r) ∘ pr₁) ((g ∘ r) ∘ pr₁)
      outer-first-evaluation = Restriction.evaluation After.first Before.first
        (FirstFactor.Coordinates.first C g r) (id₌ ((g ∘ r) ∘ pr₁))

      opaque
        outer-first-compatible : Compatible-One input-diagram outer-first-evaluation
        outer-first-compatible =
          (comp₌-unitˡ-One (FirstFactor.Coordinates.first C g r ∙ (Before.first ▷ sC))) ⁻¹ ∙
            FirstCoordinate.compatible ⁻¹

      outer-second-evaluation : Evaluation input-diagram (mapEval ∘ Before.inner-input) (uncurry f)
        (uncurry (f ∘ r)) (uncurry (f ∘ r))
      outer-second-evaluation = Restriction.evaluation After.inner-evaluation Before.inner-evaluation
        ((uncurry-restrict f r) ⁻¹) (id₌ (uncurry (f ∘ r)))

      opaque
        outer-second-compatible : Compatible-One input-diagram outer-second-evaluation
        outer-second-compatible =
          (comp₌-unitˡ-One ((uncurry-restrict f r) ⁻¹ ∙ (Before.inner-evaluation ▷ sC))) ⁻¹ ∙
            inner-evaluation-square ⁻¹

      opaque
        pair-input-natural : {R : CAT Γ} {p p′ : MAP R P} {z z′ : MAP R D}
          (α : p =₁ p′) (β : z =₁ z′)
          → SquareCell₌ (Before.outer-map ◁ pair⁼ α β) (pair⁼ (g ◁ α) β)
              (FirstFactor.PairInput.at-pair g p z) (FirstFactor.PairInput.at-pair g p′ z′)
        pair-input-natural α β = paste-square₌ (productMap-pair-inner-One g (id D) α β)
          (pair⁼-square (unconst-sides₌ (identity-square₌ (g ◁ α)))
            (unconst-sides₌ (postWhisker-id β)))

      input-pair = FirstFactor.PairInput.at-pair r pr₁ (uncurry (f ∘ r))
      input-last = pair⁼ (id₌ (r ∘ pr₁)) (uncurry-restrict f r)

      opaque
        input-normalization : evaluation-input =₂ (input-last ∙ input-pair)
        input-normalization =
          let first = id₌ (r ∘ pr₁)
              unit = comp-unitˡ (uncurry (f ∘ r))
              base = productMap-pair r (id D) pr₁ (uncurry (f ∘ r))
          in comp₌-assoc input-last (pair⁼ first unit) base ∙
            (comp₌-cong (pair⁼-comp first first (uncurry-restrict f r) unit) (id₌ base) ∙
              comp₌-cong (pair⁼-cong ((comp₌-unitˡ-One first) ⁻¹) (id₌ (uncurry-restrict f r ∙ unit)))
                (id₌ base))

      output-pair = FirstFactor.PairInput.at-pair g (r ∘ pr₁) (uncurry f ∘ sC)
      output-coordinate = pair⁼
        ((g ◁ pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc sC pr₁ g)
        (id₌ (uncurry f ∘ sC)) ∙ pair-pre (g ∘ pr₁) (uncurry f) sC

      opaque
        output-normalization :
          (output-pair ∙ ((Before.outer-map ◁ evaluation-output) ∙
            comp-assoc sC Before.evaluated-inner Before.outer-map)) =₂
            (output-coordinate ∙ (Before.right-normalization ▷ sC))
        output-normalization =
          let projection = pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)
              unchanged = id₌ (uncurry f ∘ sC)
              changed = pair⁼ (g ◁ projection) unchanged
              original = FirstFactor.PairInput.at-pair g (pr₁ ∘ sC) (uncurry f ∘ sC)
              input = Before.outer-map ◁ pair⁼ projection unchanged
              pre = Before.outer-map ◁ pair-pre pr₁ (uncurry f) sC
              corner = comp-assoc sC Before.evaluated-inner Before.outer-map
              tail = pre ∙ corner
              image-before = Before.right-normalization ▷ sC
              target-pre = pair-pre (g ∘ pr₁) (uncurry f) sC
              target-first = comp-assoc sC pr₁ g
              target-pair = pair⁼ target-first unchanged
              change-normalization = comp₌-assoc input pre corner ∙
                comp₌-cong (postWhisker-comp₌ Before.outer-map
                  (pair⁼ projection unchanged) (pair-pre pr₁ (uncurry f) sC)) (id₌ corner)
              natural = pair-input-natural projection unchanged
              merge = pair⁼-cong (id₌ ((g ◁ projection) ∙ target-first))
                  (comp₌-unitˡ-One unchanged) ∙
                (pair⁼-comp (g ◁ projection) target-first unchanged unchanged) ⁻¹
              normalize-target = (comp₌-assoc
                  (pair⁼ ((g ◁ projection) ∙ target-first) unchanged) target-pre image-before) ⁻¹ ∙
                (comp₌-cong merge (id₌ (target-pre ∙ image-before)) ∙
                  (comp₌-assoc changed target-pair (target-pre ∙ image-before)) ⁻¹)
          in normalize-target ∙
            (comp₌-cong (id₌ changed) (FirstFactor.at-pair-restrict g pr₁ (uncurry f) sC) ∙
            (comp₌-assoc changed original tail ∙
            (comp₌-cong natural (id₌ tail) ∙
            ((comp₌-assoc output-pair input tail) ⁻¹ ∙
              comp₌-cong (id₌ output-pair) change-normalization))))

```

For the right normalization, both routes are compared after the independent
target frame built from the associator and the actual uncurrying restriction.
The input and output frames retain their chosen product comparisons. After
normalizing both routes to the same coordinate route, canceling the target
frame gives the right-normalization square.

```agda
      restricted-inner : MAP (Q × C) D
      restricted-inner = uncurry (f ∘ r)
      changed-inner : MAP (Q × C) D
      changed-inner = uncurry f ∘ sC
      evaluation-step : restricted-inner =₁ changed-inner
      evaluation-step = uncurry-restrict f r
      first-corner : ((g ∘ r) ∘ pr₁ {C = Q} {D = C}) =₁ (g ∘ (r ∘ pr₁))
      first-corner = comp-assoc (pr₁ {C = Q} {D = C}) r g
      target-change : pair ((g ∘ r) ∘ pr₁) restricted-inner =₁
        pair ((g ∘ r) ∘ pr₁) changed-inner
      target-change = pair⁼ (id₌ ((g ∘ r) ∘ pr₁)) evaluation-step
      target-corner : pair ((g ∘ r) ∘ pr₁) changed-inner =₁
        pair (g ∘ (r ∘ pr₁)) changed-inner
      target-corner = pair⁼ first-corner (id₌ changed-inner)
      target-frame : pair ((g ∘ r) ∘ pr₁) restricted-inner =₁
        pair (g ∘ (r ∘ pr₁)) changed-inner
      target-frame = target-corner ∙ target-change

      input-frame : (Before.outer-map ∘ sD) ∘ After.evaluated-inner =₁
        (Before.outer-map ∘ common)
      input-frame = (Before.outer-map ◁ evaluation-input) ∙
        comp-assoc After.evaluated-inner sD Before.outer-map
      output-frame : (Before.outer-map ∘ Before.evaluated-inner) ∘ sC =₁
        (Before.outer-map ∘ common)
      output-frame = (Before.outer-map ◁ evaluation-output) ∙
        comp-assoc sC Before.evaluated-inner Before.outer-map

      opaque
        input-frame-normalization : (output-pair ∙ input-frame) =₂
          (target-frame ∙ (After.right-normalization ∙ (outer-change ▷ After.evaluated-inner)))
        input-frame-normalization =
          let image-step : pair (g ∘ (r ∘ pr₁)) restricted-inner =₁
                pair (g ∘ (r ∘ pr₁)) changed-inner
              image-step = pair⁼ (id₌ (g ∘ (r ∘ pr₁))) evaluation-step
              restricted-pair : (Before.outer-map ∘ pair (r ∘ pr₁) restricted-inner) =₁
                pair (g ∘ (r ∘ pr₁)) restricted-inner
              restricted-pair = FirstFactor.PairInput.at-pair g (r ∘ pr₁) restricted-inner
              restricted-corner : pair ((g ∘ r) ∘ pr₁) restricted-inner =₁
                pair (g ∘ (r ∘ pr₁)) restricted-inner
              restricted-corner = pair⁼ first-corner (id₌ restricted-inner)
              first : (Before.outer-map ∘ pair (r ∘ pr₁) restricted-inner) =₁
                (Before.outer-map ∘ common)
              first = Before.outer-map ◁ input-last
              second : (Before.outer-map ∘ (sD ∘ After.evaluated-inner)) =₁
                (Before.outer-map ∘ pair (r ∘ pr₁) restricted-inner)
              second = Before.outer-map ◁ input-pair
              corner : ((Before.outer-map ∘ sD) ∘ After.evaluated-inner) =₁
                (Before.outer-map ∘ (sD ∘ After.evaluated-inner))
              corner = comp-assoc After.evaluated-inner sD Before.outer-map
              tail : ((Before.outer-map ∘ sD) ∘ After.evaluated-inner) =₁
                (Before.outer-map ∘ pair (r ∘ pr₁) restricted-inner)
              tail = second ∙ corner
              after : ((Before.outer-map ∘ sD) ∘ After.evaluated-inner) =₁
                pair ((g ∘ r) ∘ pr₁) restricted-inner
              after = After.right-normalization ∙ (outer-change ▷ After.evaluated-inner)
              natural : SquareCell₌ first image-step restricted-pair output-pair
              natural = replace-edges₌ (id₌ first)
                (pair⁼-cong (postWhisker-id₌ g (r ∘ pr₁)) (id₌ evaluation-step))
                (pair-input-natural (id₌ (r ∘ pr₁)) evaluation-step)
              image-square : (image-step ∙ restricted-corner) =₂ target-frame
              image-square = pair⁼-square
                (unconst-sides₌ (identity-square₌ first-corner))
                (transpose-square₌ (unconst-sides₌ (identity-square₌ evaluation-step)))
              frame-normalization : input-frame =₂ (first ∙ tail)
              frame-normalization = comp₌-assoc first second corner ∙
                comp₌-cong (postWhisker-comp₌ Before.outer-map input-last input-pair ∙
                  (postWhisker Before.outer-map ◁ input-normalization)) (id₌ corner)
              through-input : (output-pair ∙ input-frame) =₂
                (image-step ∙ (restricted-corner ∙ after))
              through-input =
                comp₌-cong (id₌ image-step) (FirstFactor.at-pair-input-change g r pr₁ restricted-inner) ∙
                (comp₌-assoc image-step restricted-pair tail ∙
                (comp₌-cong natural (id₌ tail) ∙
                ((comp₌-assoc output-pair first tail) ⁻¹ ∙
                  comp₌-cong (id₌ output-pair) frame-normalization)))
          in comp₌-cong image-square (id₌ after) ∙
            ((comp₌-assoc image-step restricted-corner after) ⁻¹ ∙ through-input)

      opaque
        target-frame-normalization : (target-frame ∙ common-change) =₂ output-coordinate
        target-frame-normalization =
          let first = FirstFactor.Coordinates.first C g r
              unchanged = id₌ changed-inner
              paired = pair⁼ first (evaluation-step ⁻¹)
              base = pair-pre (g ∘ pr₁) (uncurry f) sC
              first-tail = (g ◁ pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc sC pr₁ g
              merge-step = pair⁼-cong (comp₌-unitˡ-One first) (comp₌-inverseʳ-One evaluation-step) ∙
                (pair⁼-comp (id₌ ((g ∘ r) ∘ pr₁)) first evaluation-step (evaluation-step ⁻¹)) ⁻¹
              merge-corner = pair⁼-cong (comp-inv-left first-corner first-tail)
                  (comp₌-unitˡ-One unchanged) ∙
                (pair⁼-comp first-corner first unchanged unchanged) ⁻¹
          in comp₌-cong merge-corner (id₌ base) ∙
            (comp₌-cong (comp₌-cong (id₌ target-corner) merge-step) (id₌ base) ∙
            ((comp₌-assoc target-corner (target-change ∙ paired) base) ⁻¹ ∙
            (comp₌-cong (id₌ target-corner) ((comp₌-assoc target-change paired base) ⁻¹) ∙
              comp₌-assoc target-corner target-change (paired ∙ base))))

      opaque
        restriction-frame-normalization : right-change =₂
          ((outer-change ▷ After.evaluated-inner) ∙ ((input-frame ⁻¹) ∙ output-frame))
        restriction-frame-normalization =
          let corner = comp-assoc After.evaluated-inner sD Before.outer-map
              old-corner = comp-assoc sC Before.evaluated-inner Before.outer-map
              input-inverse = Before.outer-map ◁ evaluation-input ⁻¹
              output = Before.outer-map ◁ evaluation-output
              back-normalization = (inverse-composite (Before.outer-map ◁ evaluation-input) corner) ⁻¹ ∙
                comp₌-cong (id₌ (corner ⁻¹)) (postWhisker-inverse Before.outer-map evaluation-input)
              change-inverse = comp₌-cong (id₌ (evaluation-input ⁻¹)) (inverse-inverse evaluation-output) ∙
                inverse-composite (evaluation-output ⁻¹) evaluation-input
              changed = postWhisker-comp₌ Before.outer-map (evaluation-input ⁻¹) evaluation-output ∙
                (postWhisker Before.outer-map ◁ change-inverse)
          in comp₌-cong (id₌ (outer-change ▷ After.evaluated-inner))
            (comp₌-cong back-normalization (id₌ output-frame) ∙
            ((comp₌-assoc (corner ⁻¹) input-inverse output-frame) ⁻¹ ∙
            (comp₌-cong (id₌ (corner ⁻¹)) (comp₌-assoc input-inverse output old-corner) ∙
              comp₌-cong (id₌ (corner ⁻¹)) (comp₌-cong changed (id₌ old-corner)))))

      opaque
        right-normalization-image : (target-frame ∙ (After.right-normalization ∙ right-change)) =₂
          (output-coordinate ∙ (Before.right-normalization ▷ sC))
        right-normalization-image =
          let chosen = outer-change ▷ After.evaluated-inner
              after = After.right-normalization ∙ chosen
              tail = input-frame ⁻¹ ∙ output-frame
          in output-normalization ∙
            (comp₌-cong (comp-inv-right output-pair input-frame) (id₌ output-frame) ∙
            ((comp₌-assoc (output-pair ∙ input-frame) (input-frame ⁻¹) output-frame) ⁻¹ ∙
            (comp₌-cong (input-frame-normalization ⁻¹) (id₌ tail) ∙
            ((comp₌-assoc target-frame after tail) ⁻¹ ∙
            (comp₌-cong (id₌ target-frame) ((comp₌-assoc After.right-normalization chosen tail) ⁻¹) ∙
              comp₌-cong (id₌ target-frame)
                (comp₌-cong (id₌ After.right-normalization) restriction-frame-normalization))))))

    opaque
      right-normalization-restrict : SquareCell₌ (Before.right-normalization ▷ sC) After.right-normalization
        right-change common-change
      right-normalization-restrict =
        (cancel-left target-frame
          (comp₌-assoc target-frame common-change (Before.right-normalization ▷ sC) ∙
            (comp₌-cong (target-frame-normalization ⁻¹) (id₌ (Before.right-normalization ▷ sC)) ∙
              right-normalization-image))) ⁻¹

    opaque
      left-normalization-restrict : SquareCell₌ (Before.left-normalization ▷ sC) After.left-normalization
        left-change common-change
      left-normalization-restrict =
        (comp₌-unitˡ-One (common-change ∙ (Before.left-normalization ▷ sC)) ∙
          (comp₌-cong (pair⁼-id-One ((g ∘ r) ∘ pr₁) (uncurry (f ∘ r)))
              (id₌ (common-change ∙ (Before.left-normalization ▷ sC))) ∙
            pair-compatible-One input-diagram outer-first-evaluation outer-second-evaluation
              outer-first-compatible outer-second-compatible)) ⁻¹
    opaque
      comparison-restrict : SquareCell₌ (Before.comparison ▷ sC) After.comparison left-change right-change
      comparison-restrict =
        let normalized = comp₌-cong (preWhisker-inverse Before.right-normalization sC)
              (id₌ (Before.left-normalization ▷ sC)) ∙
              preWhisker-comp₌ (Before.right-normalization ⁻¹) Before.left-normalization sC
        in replace-edges₌ (normalized ⁻¹) (id₌ After.comparison)
          (inv-comp-square₌ left-normalization-restrict right-normalization-restrict)

    private
      opaque
        comparison-triangle-square : SquareCell₌ (Before.outer-input ◁ input-change) right-change
          (restrict-triangle Before.outer-input Before.input Before.comparison sC) After.comparison
        comparison-triangle-square =
          let across = Before.outer-input ◁ input-change
              corner = comp-assoc sC Before.input Before.outer-input
              before = Before.comparison ▷ sC
              after = After.comparison
              collapse : ((after ∙ (across ∙ corner)) ∙ corner ⁻¹) =₂ (after ∙ across)
              collapse = comp₌-cong (id₌ after) (comp-inv-right across corner) ∙
                comp₌-assoc after (across ∙ corner) (corner ⁻¹)
          in comp₌-assoc right-change before (corner ⁻¹) ∙
            (comp₌-cong (comparison-restrict ⁻¹) (id₌ (corner ⁻¹)) ∙ collapse ⁻¹)

    opaque
      post-comparison-restrict : SquareCell₌
        (post-triangle mapEval Before.outer-input Before.input Before.comparison ▷ sC)
        (post-triangle mapEval After.outer-input After.input After.comparison)
        ((doubleEvaluation ◁ input-change) ∙ comp-assoc sC Before.input doubleEvaluation)
        ((mapEval ◁ right-change) ∙ comp-assoc sC (Before.outer-map ∘ Before.evaluated-inner) mapEval)
      post-comparison-restrict =
        (post-triangle-change mapEval Before.outer-input Before.input sC After.input input-change
          Before.comparison After.comparison right-change comparison-triangle-square) ⁻¹ ∙
        comp₌-assoc (mapEval ◁ right-change)
          (comp-assoc sC (Before.outer-map ∘ Before.evaluated-inner) mapEval)
          (post-triangle mapEval Before.outer-input Before.input Before.comparison ▷ sC)


    private
      inner-frame : ((Before.outer-map ∘ sD) ∘ After.evaluated-inner) =₁
        ((Before.outer-map ∘ Before.evaluated-inner) ∘ sC)
      inner-frame = post-square-cell Before.outer-map sC Before.evaluated-inner sD
        After.evaluated-inner evaluation-change

      outer-frame : (uncurry g ∘ sD) =₁ uncurry (g ∘ r)
      outer-frame = post-triangle mapEval Before.outer-map sD outer-change

      native-inner-frame : ((uncurry g ∘ sD) ∘ After.evaluated-inner) =₁
        ((uncurry g ∘ Before.evaluated-inner) ∘ sC)
      native-inner-frame = post-square-cell (uncurry g) sC Before.evaluated-inner sD
        After.evaluated-inner evaluation-change

      opaque
        outer-frame-normalization : outer-frame =₂ ((uncurry-restrict g r) ⁻¹)
        outer-frame-normalization =
          (inverse-unique (uncurry-restrict g r) outer-frame
            ((const-One (id₌ (uncurry (g ∘ r)))) ⁻¹ ∙
              post-triangle-inverse mapEval Before.outer-map sD outer-change)) ⁻¹

        inner-frame-inverse-normalization : (inner-frame ⁻¹) =₂
          ((comp-assoc After.evaluated-inner sD Before.outer-map) ⁻¹ ∙
            ((Before.outer-map ◁ evaluation-change ⁻¹) ∙
              comp-assoc sC Before.evaluated-inner Before.outer-map))
        inner-frame-inverse-normalization =
          let corner = comp-assoc After.evaluated-inner sD Before.outer-map
              output-corner = comp-assoc sC Before.evaluated-inner Before.outer-map
              image = Before.outer-map ◁ evaluation-change
              back = Before.outer-map ◁ evaluation-change ⁻¹
              triangle = image ∙ corner
              triangle-inverse : (triangle ⁻¹) =₂ ((corner ⁻¹) ∙ back)
              triangle-inverse =
                comp₌-cong (id₌ (corner ⁻¹)) ((postWhisker-inverse Before.outer-map evaluation-change) ⁻¹) ∙
                  inverse-composite image corner
          in comp₌-assoc (corner ⁻¹) back output-corner ∙
            (comp₌-cong triangle-inverse (inverse-inverse output-corner) ∙
              inverse-composite (output-corner ⁻¹) triangle)

        right-change-factorization : right-change =₂
          ((outer-change ▷ After.evaluated-inner) ∙ (inner-frame ⁻¹))
        right-change-factorization =
          comp₌-cong (id₌ (outer-change ▷ After.evaluated-inner))
            (inner-frame-inverse-normalization ⁻¹)

        inner-frame-evaluation : SquareCell₌
          (comp-assoc sD Before.outer-map mapEval ▷ After.evaluated-inner)
          (comp-assoc Before.evaluated-inner Before.outer-map mapEval ▷ sC)
          native-inner-frame
          (post-square-cell mapEval sC (Before.outer-map ∘ Before.evaluated-inner)
            (Before.outer-map ∘ sD) After.evaluated-inner inner-frame)
        inner-frame-evaluation = post-square-cell-comp sC Before.evaluated-inner sD
          After.evaluated-inner evaluation-change Before.outer-map mapEval

    native-right-change : ((uncurry g ∘ Before.evaluated-inner) ∘ sC) =₁
      (uncurry (g ∘ r) ∘ After.evaluated-inner)
    native-right-change = ((uncurry-restrict g r ▷ After.evaluated-inner) ⁻¹) ∙
      ((comp-assoc After.evaluated-inner sD (uncurry g)) ⁻¹ ∙
        (((uncurry g) ◁ evaluation-change ⁻¹) ∙
          comp-assoc sC Before.evaluated-inner (uncurry g)))

    private
      image-inner-frame : ((mapEval ∘ (Before.outer-map ∘ sD)) ∘ After.evaluated-inner) =₁
        ((mapEval ∘ (Before.outer-map ∘ Before.evaluated-inner)) ∘ sC)
      image-inner-frame = post-square-cell mapEval sC (Before.outer-map ∘ Before.evaluated-inner)
        (Before.outer-map ∘ sD) After.evaluated-inner inner-frame

      outer-image : ((mapEval ∘ (Before.outer-map ∘ sD)) ∘ After.evaluated-inner) =₁
        (mapEval ∘ (After.outer-map ∘ After.evaluated-inner))
      outer-image = post-triangle mapEval (Before.outer-map ∘ sD) After.evaluated-inner
        (outer-change ▷ After.evaluated-inner)

      raw-right-change : ((mapEval ∘ (Before.outer-map ∘ Before.evaluated-inner)) ∘ sC) =₁
        (mapEval ∘ (After.outer-map ∘ After.evaluated-inner))
      raw-right-change = post-triangle mapEval (Before.outer-map ∘ Before.evaluated-inner) sC right-change

      opaque
        native-inner-frame-inverse-normalization : (native-inner-frame ⁻¹) =₂
          ((comp-assoc After.evaluated-inner sD (uncurry g)) ⁻¹ ∙
            (((uncurry g) ◁ evaluation-change ⁻¹) ∙ comp-assoc sC Before.evaluated-inner (uncurry g)))
        native-inner-frame-inverse-normalization =
          let corner = comp-assoc After.evaluated-inner sD (uncurry g)
              output-corner = comp-assoc sC Before.evaluated-inner (uncurry g)
              image = (uncurry g) ◁ evaluation-change
              back = (uncurry g) ◁ evaluation-change ⁻¹
              triangle = image ∙ corner
              triangle-inverse : (triangle ⁻¹) =₂ ((corner ⁻¹) ∙ back)
              triangle-inverse =
                comp₌-cong (id₌ (corner ⁻¹)) ((postWhisker-inverse (uncurry g) evaluation-change) ⁻¹) ∙
                  inverse-composite image corner
          in comp₌-assoc (corner ⁻¹) back output-corner ∙
            (comp₌-cong triangle-inverse (inverse-inverse output-corner) ∙
              inverse-composite (output-corner ⁻¹) triangle)

        image-inner-frame-inverse-normalization : (image-inner-frame ⁻¹) =₂
          ((comp-assoc After.evaluated-inner (Before.outer-map ∘ sD) mapEval) ⁻¹ ∙
            ((mapEval ◁ inner-frame ⁻¹) ∙ comp-assoc sC (Before.outer-map ∘ Before.evaluated-inner) mapEval))
        image-inner-frame-inverse-normalization =
          let corner = comp-assoc After.evaluated-inner (Before.outer-map ∘ sD) mapEval
              output-corner = comp-assoc sC (Before.outer-map ∘ Before.evaluated-inner) mapEval
              image = mapEval ◁ inner-frame
              back = mapEval ◁ inner-frame ⁻¹
              triangle = image ∙ corner
              triangle-inverse : (triangle ⁻¹) =₂ ((corner ⁻¹) ∙ back)
              triangle-inverse =
                comp₌-cong (id₌ (corner ⁻¹)) ((postWhisker-inverse mapEval inner-frame) ⁻¹) ∙
                  inverse-composite image corner
          in comp₌-assoc (corner ⁻¹) back output-corner ∙
            (comp₌-cong triangle-inverse (inverse-inverse output-corner) ∙
              inverse-composite (output-corner ⁻¹) triangle)

        raw-right-factorization : raw-right-change =₂ (outer-image ∙ (image-inner-frame ⁻¹))
        raw-right-factorization =
          let chosen = outer-change ▷ After.evaluated-inner
              image-chosen = mapEval ◁ chosen
              corner = comp-assoc After.evaluated-inner (Before.outer-map ∘ sD) mapEval
              back = mapEval ◁ inner-frame ⁻¹
              output-corner = comp-assoc sC (Before.outer-map ∘ Before.evaluated-inner) mapEval
              tail = back ∙ output-corner
              merge : ((image-chosen ∙ back) ∙ output-corner) =₂ raw-right-change
              merge = comp₌-cong ((postWhisker mapEval ◁ right-change-factorization) ⁻¹)
                  (id₌ output-corner) ∙
                comp₌-cong ((postWhisker-comp₌ mapEval chosen (inner-frame ⁻¹)) ⁻¹)
                  (id₌ output-corner)
          in (merge ∙
            ((comp₌-assoc image-chosen back output-corner) ⁻¹ ∙
            (comp₌-cong (comp-inv-right image-chosen corner) (id₌ tail) ∙
            ((comp₌-assoc outer-image (corner ⁻¹) tail) ⁻¹ ∙
              comp₌-cong (id₌ outer-image) image-inner-frame-inverse-normalization)))) ⁻¹

        outer-action-normalization :
          (outer-image ∙ (comp-assoc sD Before.outer-map mapEval ▷ After.evaluated-inner)) =₂
          (comp-assoc After.evaluated-inner After.outer-map mapEval ∙
            ((uncurry-restrict g r ▷ After.evaluated-inner) ⁻¹))
        outer-action-normalization =
          let chosen = mapEval ◁ outer-change
              corner = comp-assoc sD Before.outer-map mapEval
              after = comp-assoc After.evaluated-inner After.outer-map mapEval
              h = After.evaluated-inner
              before = corner ▷ h
              normalized : ((chosen ▷ h) ∙ before) =₂ ((uncurry-restrict g r ▷ h) ⁻¹)
              normalized = preWhisker-inverse (uncurry-restrict g r) h ∙
                ((preWhisker h ◁ outer-frame-normalization) ∙
                  (preWhisker-comp₌ chosen corner h) ⁻¹)
          in comp₌-cong (id₌ after) normalized ∙
            (comp₌-assoc after (chosen ▷ h) before ∙
              comp₌-cong ((whisker-mixed-One outer-change h mapEval) ⁻¹) (id₌ before))

    opaque
      target-frame-restrict : SquareCell₌
        (comp-assoc Before.evaluated-inner Before.outer-map mapEval ▷ sC)
        (comp-assoc After.evaluated-inner After.outer-map mapEval)
        native-right-change raw-right-change
      target-frame-restrict =
        let before = comp-assoc Before.evaluated-inner Before.outer-map mapEval ▷ sC
            after = comp-assoc After.evaluated-inner After.outer-map mapEval
            middle = comp-assoc sD Before.outer-map mapEval ▷ After.evaluated-inner
            outer-back = (uncurry-restrict g r ▷ After.evaluated-inner) ⁻¹
        in comp₌-cong (id₌ after)
              (comp₌-cong (id₌ outer-back) native-inner-frame-inverse-normalization) ∙
          (comp₌-assoc after outer-back (native-inner-frame ⁻¹) ∙
          (comp₌-cong outer-action-normalization (id₌ (native-inner-frame ⁻¹)) ∙
          ((comp₌-assoc outer-image middle (native-inner-frame ⁻¹)) ⁻¹ ∙
          (comp₌-cong (id₌ outer-image) (inverse-square₌ inner-frame-evaluation) ∙
          (comp₌-assoc outer-image (image-inner-frame ⁻¹) before ∙
            comp₌-cong raw-right-factorization (id₌ before))))))

      evaluation-coordinate-restrict : SquareCell₌ (Before.evaluation ▷ sC) After.evaluation
        ((doubleEvaluation ◁ input-change) ∙ comp-assoc sC Before.input doubleEvaluation)
        native-right-change
      evaluation-coordinate-restrict =
        let frame = comp-assoc Before.evaluated-inner Before.outer-map mapEval
            triangle = post-triangle mapEval Before.outer-input Before.input Before.comparison
            normalized = comp₌-cong (preWhisker-inverse frame sC) (id₌ (triangle ▷ sC)) ∙
              preWhisker-comp₌ (frame ⁻¹) triangle sC
            target-square = transpose-square₌ (inverse-square₌ (transpose-square₌ target-frame-restrict))
        in replace-edges₌ (normalized ⁻¹) (id₌ After.evaluation)
          (adjoin-square₌ post-comparison-restrict target-square)


    private
      paired-before : MAP P Before.K
      paired-before = pair g f
      paired-middle : MAP Q Before.K
      paired-middle = paired-before ∘ r
      paired-after : MAP Q Before.K
      paired-after = pair (g ∘ r) (f ∘ r)
      paired-change : paired-middle =₁ paired-after
      paired-change = pair-pre g f r
      universal-uncurry : MAP (Before.K × C) E
      universal-uncurry = uncurry (mapComp {C = C} {D = D} {E = E})
      before-uncurry : uncurry (compose g f) =₁ (universal-uncurry ∘ Before.input)
      before-uncurry = uncurry-restrict mapComp paired-before
      middle-uncurry : uncurry (mapComp ∘ paired-middle) =₁
        (universal-uncurry ∘ productMap paired-middle (id C))
      middle-uncurry = uncurry-restrict mapComp paired-middle
      after-uncurry : uncurry (compose (g ∘ r) (f ∘ r)) =₁
        (universal-uncurry ∘ After.input)
      after-uncurry = uncurry-restrict mapComp paired-after
      source-restrict : uncurry (compose g f ∘ r) =₁ (uncurry (compose g f) ∘ sC)
      source-restrict = uncurry-restrict (compose g f) r
      source-action : uncurry (compose g f ∘ r) =₁ uncurry (compose (g ∘ r) (f ∘ r))
      source-action = uncurry⁼ (compose-pre g f r)
      source-change : (uncurry (compose g f) ∘ sC) =₁
        uncurry (compose (g ∘ r) (f ∘ r))
      source-change = source-action ∙ source-restrict ⁻¹
      input-uncurry-change : ((universal-uncurry ∘ Before.input) ∘ sC) =₁
        (universal-uncurry ∘ After.input)
      input-uncurry-change = (universal-uncurry ◁ input-change) ∙
        comp-assoc sC Before.input universal-uncurry

      opaque
        source-substitution : SquareCell₌ (uncurry⁼ (mapComp ◁ paired-change))
          (universal-uncurry ◁ productMap-cong paired-change (id₌ (id C)))
          middle-uncurry after-uncurry
        source-substitution = replace-edges₌ (id₌ (uncurry⁼ (mapComp ◁ paired-change)))
          (postWhisker universal-uncurry ◁
            productMap-cong₂ (id₌ paired-change) (const-One (id₌ (id C))))
          (unconst-sides₌ (uncurry-restrict-substitution mapComp paired-change))

        source-full-image : (after-uncurry ∙ source-action) =₂
          (input-uncurry-change ∙ ((before-uncurry ▷ sC) ∙ source-restrict))
        source-full-image =
          let action = uncurry⁼ (mapComp ◁ paired-change)
              corner-action = uncurry⁼ (comp-assoc r paired-before mapComp)
              first = universal-uncurry ◁ productMap-cong paired-change (id₌ (id C))
              second = universal-uncurry ◁ productMap-first-comp paired-before r
              corner = comp-assoc sC Before.input universal-uncurry
              tail = (before-uncurry ▷ sC) ∙ source-restrict
              iterate : (middle-uncurry ∙ corner-action) =₂ (second ∙ (corner ∙ tail))
              iterate = uncurry-restrict-iterated mapComp paired-before r
          in (comp₌-assoc (universal-uncurry ◁ input-change) corner tail) ⁻¹ ∙
            (comp₌-cong ((postWhisker-comp₌ universal-uncurry
                (productMap-cong paired-change (id₌ (id C)))
                (productMap-first-comp paired-before r)) ⁻¹) (id₌ (corner ∙ tail)) ∙
            ((comp₌-assoc first second (corner ∙ tail)) ⁻¹ ∙
            (comp₌-cong (id₌ first) iterate ∙
            (comp₌-assoc first middle-uncurry corner-action ∙
            (comp₌-cong source-substitution (id₌ corner-action) ∙
            ((comp₌-assoc after-uncurry action corner-action) ⁻¹ ∙
              comp₌-cong (id₌ after-uncurry)
                (uncurry⁼-composition (mapComp ◁ paired-change)
                  (comp-assoc r paired-before mapComp))))))))

        source-frame-restrict : SquareCell₌ (before-uncurry ▷ sC) after-uncurry
          source-change input-uncurry-change
        source-frame-restrict =
          let before = before-uncurry ▷ sC
              collapse : ((input-uncurry-change ∙ (before ∙ source-restrict)) ∙
                  source-restrict ⁻¹) =₂ (input-uncurry-change ∙ before)
              collapse = comp-inv-right (input-uncurry-change ∙ before) source-restrict ∙
                comp₌-cong ((comp₌-assoc input-uncurry-change before source-restrict) ⁻¹)
                  (id₌ (source-restrict ⁻¹))
          in comp₌-assoc after-uncurry source-action (source-restrict ⁻¹) ∙
            (comp₌-cong (source-full-image ⁻¹) (id₌ (source-restrict ⁻¹)) ∙ collapse ⁻¹)

        fixed-beta-restrict : SquareCell₌ ((mapComp-β ▷ Before.input) ▷ sC)
          (mapComp-β ▷ After.input) input-uncurry-change
          ((doubleEvaluation ◁ input-change) ∙ comp-assoc sC Before.input doubleEvaluation)
        fixed-beta-restrict = replace-sides₌
          (comp₌-cong (id₌ (universal-uncurry ◁ input-change))
            (const-One (comp-assoc sC Before.input universal-uncurry)))
          (comp₌-cong (id₌ (doubleEvaluation ◁ input-change))
            (const-One (comp-assoc sC Before.input doubleEvaluation)))
          (identification-restriction mapComp-β Before.input sC After.input input-change)

    opaque
      composition-evaluation-restrict-square : SquareCell₌ (composition-evaluation g f ▷ sC)
        (composition-evaluation (g ∘ r) (f ∘ r)) source-change native-right-change
      composition-evaluation-restrict-square =
        let beta = mapComp-β ▷ Before.input
            coordinate = Before.evaluation
            source-normalized : (composition-evaluation g f ▷ sC) =₂
              ((coordinate ▷ sC) ∙ ((beta ▷ sC) ∙ (before-uncurry ▷ sC)))
            source-normalized =
              comp₌-cong (id₌ (coordinate ▷ sC)) (preWhisker-comp₌ beta before-uncurry sC) ∙
                preWhisker-comp₌ coordinate (beta ∙ before-uncurry) sC
        in replace-edges₌ (source-normalized ⁻¹) (id₌ (composition-evaluation (g ∘ r) (f ∘ r)))
          (adjoin-square₌ (adjoin-square₌ source-frame-restrict fixed-beta-restrict)
            evaluation-coordinate-restrict)

      composition-evaluation-restrict :
        (composition-evaluation (g ∘ r) (f ∘ r) ∙ uncurry⁼ (compose-pre g f r)) =₂
        (native-right-change ∙
          ((composition-evaluation g f ▷ sC) ∙ uncurry-restrict (compose g f) r))
      composition-evaluation-restrict =
        let before = composition-evaluation g f ▷ sC
            after = composition-evaluation (g ∘ r) (f ∘ r)
            collapse : ((after ∙ source-change) ∙ source-restrict) =₂ (after ∙ source-action)
            collapse = comp₌-cong (id₌ after) (inv-comp-right source-action source-restrict) ∙
              comp₌-assoc after source-change source-restrict
        in comp₌-assoc native-right-change before source-restrict ∙
          (comp₌-cong (composition-evaluation-restrict-square ⁻¹) (id₌ source-restrict) ∙
            collapse ⁻¹)
```
