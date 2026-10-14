# Composition under restriction

The selected composition comparison is lifted using the specified pairing
identifications over the base. Restriction compares the actual
route through the changed composition with the route through evaluation at
the original source. Both literal routes carry independently constructed
compatibility over the base. Their underlying equality follows from the two
projections; no equality of higher proof fields is asserted.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CompositionRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; inv₌; comp-assoc; comp-unitˡ; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus using (pair⁼; pair-pre; project-pair₂)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One; cancel-left; cancel-right; inverse-composite;
    inverse-inverse; postWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; lies-over-comp; restrict-square-One; restrict-change-square-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-comp; pair⁼-cong; pair⁼-triangle₂-One; pair₌-extensionality)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution as FirstFactor
open import SCT.VolumeI.Chapter01.Section03.Squares using (square; comp-square; module Square)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
  using (CategoryOverBase; FunctorOverBase; FunctorOverMap; comp-over; comp-over-map)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (IdentificationOver; identification-over; comp-identification-over;
    inverse-identification-over; identification-over-pre; compatible-inverse;
    IsIdentificationOver; postcompose-over; identification-over-post;
    identification-over-postcompose; identification-over-paste; postcompose-compose;
    over-to-compatible; module ProjectedPasting)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase
  using (change-parameter; second-projection; module OverFirstFactor)
open import SCT.VolumeI.Chapter01.Section04.Currying using (uncurry-restrict; uncurry⁼)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Composition using (compose; compose-pre)
open import SCT.VolumeI.Chapter01.Section04.CompositionEvaluation using (composition-evaluation)
import SCT.VolumeI.Chapter01.Section04.CompositionEvaluation as Direct
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase
  using (evaluation-over; evaluation-compose; evaluation⁼; evaluation⁼-over)
open import SCT.VolumeI.Chapter01.Section04.EvaluationRestriction
  using (evaluation-restrict; evaluation-restrict-over)

private
  module ChosenProjections {Γ : Context} {P Q C D : CAT Γ}
    (r : MAP Q P) (x : MAP P (Map C D)) where
    source-change : MAP (Q × C) (P × C)
    source-change = productMap r (id C)
    target-change : MAP (Q × D) (P × D)
    target-change = productMap r (id D)
    before = pair pr₁ (uncurry x)
    after = pair pr₁ (uncurry (x ∘ r))
    change = uncurry-restrict x r
    base = productMap-pair r (id D) pr₁ (uncurry (x ∘ r))
    input = pair⁼ (id₌ (r ∘ pr₁)) (change ∙ comp-unitˡ (uncurry (x ∘ r))) ∙ base
    output = pair⁼ (pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)) (id₌ (uncurry x ∘ source-change)) ∙
      pair-pre pr₁ (uncurry x) source-change
    paired = FirstFactor.PairInput.at-pair r pr₁ (uncurry (x ∘ r))
    last = pair⁼ (id₌ (r ∘ pr₁)) change
    initial = pair-β₂ pr₁ (uncurry (x ∘ r)) ∙
      restrict-triangle pr₂ target-change (second-projection r) after
    final = restrict-triangle pr₂ before (pair-β₂ pr₁ (uncurry x)) source-change
    common-β = pair-β₂ (r ∘ pr₁) (uncurry x ∘ source-change)
    paired-β = pair-β₂ (r ∘ pr₁) (uncurry (x ∘ r))
    raw-initial = project-pair₂ (r ∘ pr₁) (id D ∘ pr₂) after

    opaque
      input-normalization : input =₂ (last ∙ paired)
      input-normalization =
        let first = id₌ (r ∘ pr₁)
            unit = comp-unitˡ (uncurry (x ∘ r))
        in comp₌-assoc last (pair⁼ first unit) base ∙
          (comp₌-cong (pair⁼-comp first first change unit) (id₌ base) ∙
            comp₌-cong (pair⁼-cong ((comp₌-unitˡ-One first) ⁻¹) (id₌ (change ∙ unit)))
              (id₌ base))

      initial-normalization : initial =₂
        ((pair-β₂ pr₁ (uncurry (x ∘ r)) ∙ (comp-unitˡ pr₂ ▷ after)) ∙ raw-initial)
      initial-normalization =
        let beta = pair-β₂ (r ∘ pr₁) (id D ∘ pr₂)
            unitor = comp-unitˡ (pr₂ {C = Q} {D = D})
            assoc = comp-assoc after target-change (pr₂ {C = P} {D = D})
        in (comp₌-assoc (pair-β₂ pr₁ (uncurry (x ∘ r))) (unitor ▷ after) raw-initial) ⁻¹ ∙
          (comp₌-cong (id₌ (pair-β₂ pr₁ (uncurry (x ∘ r))))
            (comp₌-assoc (unitor ▷ after) (beta ▷ after) (assoc ⁻¹) ∙
              comp₌-cong (preWhisker-comp₌ unitor beta after) (id₌ (assoc ⁻¹))))

      input-projection : SquareCell₌ (pr₂ ◁ input) change initial common-β
      input-projection =
        let raw = lies-over-comp pr₂
              (FirstFactor.at-pair-projection₂ r pr₁ (uncurry (x ∘ r)))
              (pair⁼-triangle₂-One (id₌ (r ∘ pr₁)) change)
            bottom-normalization = FirstFactor.pair-input-second-normalization r pr₁ (uncurry (x ∘ r))
            raw-normalized : SquareCell₌ (pr₂ ◁ (last ∙ paired)) change initial common-β
            raw-normalized = comp₌-cong (id₌ change) (initial-normalization ⁻¹) ∙
              (comp₌-assoc change
                (pair-β₂ pr₁ (uncurry (x ∘ r)) ∙ (comp-unitˡ pr₂ ▷ after)) raw-initial ∙
                (comp₌-cong (comp₌-cong (id₌ change) bottom-normalization) (id₌ raw-initial) ∙ raw))
        in raw-normalized ∙ comp₌-cong (id₌ common-β) (postWhisker pr₂ ◁ input-normalization)

      output-projection : (common-β ∙ (pr₂ ◁ output)) =₂ final
      output-projection = comp₌-unitˡ-One final ∙
        pair-evaluation-over₂-One pr₁ (uncurry x) source-change
          (pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)) (id₌ (uncurry x ∘ source-change))

      evaluation-projection : SquareCell₌ (pr₂ ◁ evaluation-restrict x r) change initial final
      evaluation-projection = replace-edges₌ (id₌ _) (comp₌-unitˡ-One change)
        (lies-over-comp pr₂ input-projection
          ((comp₌-unitˡ-One common-β) ⁻¹ ∙
            compatible-inverse pr₂ final common-β output output-projection))

  opaque
    composition-projection : {Γ : Context} {P C D E : CAT Γ}
      (g : MAP P (Map D E)) (f : MAP P (Map C D))
      → SquareCell₌ (pr₂ ◁ IdentificationOver.identification (evaluation-compose g f))
          (composition-evaluation g f)
          (pair-β₂ pr₁ (uncurry (compose g f)))
          (OverFirstFactor.composite-β₂ P (uncurry g) (uncurry f))
    composition-projection {P = P} g f =
      let open OverFirstFactor P
          middle-β = pair-pr₁-β₂ (uncurry g ∘ pair-pr₁ (uncurry f))
          composite-β = composite-β₂ (uncurry g) (uncurry f)
          compose-pair = pair-pr₁-compose (uncurry g) (uncurry f)
      in replace-edges₌ (id₌ _) (comp₌-unitˡ-One (composition-evaluation g f))
        (lies-over-comp pr₂
          (pair⁼-triangle₂-One (id₌ pr₁) (composition-evaluation g f))
          ((comp₌-unitˡ-One middle-β) ⁻¹ ∙
            compatible-inverse pr₂ composite-β middle-β compose-pair
              (pair-pr₁-compose-β₂ (uncurry g) (uncurry f))))

private
  module _ {Γ : Context} {S T : CAT Γ} (k : MAP S T) where
    opaque
      change-cell : {X Y : CategoryOverBase S} {Z : CategoryOverBase T}
        (K : FunctorOverMap k Y Z) (F : FunctorOverBase X Y)
        → FunctorOverBase.cell (comp-over-map k K F) =₂
            FunctorOverBase.cell (comp-over K (postcompose-over k F))
      change-cell {Y = Y} {Z} K F =
        let open FunctorOverBase
            tail = (cell K ▷ functor F) ∙
              (comp-assoc (functor F) (functor K) (CategoryOverBase.map Z)) ⁻¹
        in (comp₌-assoc (k ◁ cell F)
          (comp-assoc (functor F) (CategoryOverBase.map Y) k) tail) ⁻¹

      change-over : {X Y : CategoryOverBase S} {Z : CategoryOverBase T}
        (K : FunctorOverMap k Y Z) {F G : FunctorOverBase X Y}
        {α : FunctorOverBase.functor F =₁ FunctorOverBase.functor G}
        → IsIdentificationOver F G α
        → IsIdentificationOver (comp-over-map k K F) (comp-over-map k K G)
            (FunctorOverBase.functor K ◁ α)
      change-over K {F} {G} given = replace-sides₌
        (const-cong ((change-cell K F) ⁻¹))
        (const-cong ((change-cell K G) ⁻¹))
        (identification-over-post K (identification-over-postcompose k given))

module CompositionUnderRestriction {Γ : Context} {P Q C D E : CAT Γ}
  (r : MAP Q P) (g : MAP P (Map D E)) (f : MAP P (Map C D)) where
  private
    sC : MAP (Q × C) (P × C)
    sC = productMap r (id C)
    sD : MAP (Q × D) (P × D)
    sD = productMap r (id D)
    sE : MAP (Q × E) (P × E)
    sE = productMap r (id E)
    Fp = FunctorOverBase.functor (evaluation-over f)
    Gp = FunctorOverBase.functor (evaluation-over g)
    Fq = FunctorOverBase.functor (evaluation-over (f ∘ r))
    Gq = FunctorOverBase.functor (evaluation-over (g ∘ r))
    Vp = IdentificationOver.identification (evaluation-compose g f)
    Vq = IdentificationOver.identification (evaluation-compose (g ∘ r) (f ∘ r))
    δ = compose-pre g f r
    Ef = evaluation-restrict f r
    Eg = evaluation-restrict g r

  source = comp-over-map r (change-parameter r) (evaluation-over (compose g f ∘ r))
  target = comp-over (comp-over (evaluation-over g) (evaluation-over f)) (change-parameter r)

  left-identification : FunctorOverBase.functor source =₁ FunctorOverBase.functor target
  left-identification = (comp-assoc sC Fp Gp) ⁻¹ ∙
    ((Gp ◁ Ef) ∙
    (comp-assoc Fq sD Gp ∙
    ((Eg ▷ Fq) ∙
    ((comp-assoc Fq Gq sE) ⁻¹ ∙
      ((sE ◁ Vq) ∙ (sE ◁ evaluation⁼ δ))))))

  right : IdentificationOver {A = One {Γ}} source target
  right = comp-identification-over
    (identification-over (Vp ▷ sC)
      (identification-over-pre (change-parameter r)
        (IdentificationOver.over (evaluation-compose g f))))
    (evaluation-restrict-over (compose g f) r)

  private
    changed-f = postcompose-over r (evaluation-over (f ∘ r))
    changed-g = postcompose-over r (evaluation-over (g ∘ r))
    changed-composite = comp-over (evaluation-over (g ∘ r)) (evaluation-over (f ∘ r))
    composite-source = comp-over-map r (change-parameter r) changed-composite
    pasted = Square.cell (comp-square (square Gq Gp Eg) (square Fq Fp Ef))
    tail = (sE ◁ Vq) ∙ (sE ◁ evaluation⁼ δ)
    normalized-left = pasted ∙ tail

    opaque
      left-normalization : normalized-left =₂ left-identification
      left-normalization =
        let first = (comp-assoc Fq Gq sE) ⁻¹
            second = Eg ▷ Fq
            third = comp-assoc Fq sD Gp
            fourth = Gp ◁ Ef
            fifth = (comp-assoc sC Fp Gp) ⁻¹
        in comp₌-cong (id₌ fifth)
            (comp₌-cong (id₌ fourth)
              (comp₌-cong (id₌ third) (comp₌-assoc second first tail) ∙
                comp₌-assoc third (second ∙ first) tail) ∙
              comp₌-assoc fourth (third ∙ (second ∙ first)) tail) ∙
            comp₌-assoc fifth (fourth ∙ (third ∙ (second ∙ first))) tail

      paste-source-cell : FunctorOverBase.cell composite-source =₂
        FunctorOverBase.cell (comp-over (change-parameter r) (comp-over changed-g changed-f))
      paste-source-cell =
        let cell-paste = postcompose-compose r (pr₁ {C = Q} {D = E}) Gq Fq
              (FunctorOverBase.cell (evaluation-over (g ∘ r)))
              (FunctorOverBase.cell (evaluation-over (f ∘ r)))
            remaining = (FunctorOverBase.cell (change-parameter {D = E} r) ▷ (Gq ∘ Fq)) ∙
              (comp-assoc (Gq ∘ Fq) sE (pr₁ {C = P} {D = E})) ⁻¹
        in comp₌-cong (cell-paste ⁻¹) (id₌ remaining) ∙
          change-cell r (change-parameter r) changed-composite

      pasted-over : IsIdentificationOver composite-source target pasted
      pasted-over = replace-sides₌ (const-cong (paste-source-cell ⁻¹)) (id₌ _)
        (identification-over-paste (change-parameter {D = C} r)
          (change-parameter {D = D} r) (change-parameter {D = E} r)
          changed-f changed-g (evaluation-over f) (evaluation-over g)
          (replace-sides₌ (const-cong (change-cell r (change-parameter r)
            (evaluation-over (f ∘ r)))) (id₌ _)
            (IdentificationOver.over (evaluation-restrict-over f r)))
          (replace-sides₌ (const-cong (change-cell r (change-parameter r)
            (evaluation-over (g ∘ r)))) (id₌ _)
            (IdentificationOver.over (evaluation-restrict-over g r))))

    normalized-left-over : IdentificationOver {A = One {Γ}} source target
    normalized-left-over = comp-identification-over (identification-over pasted pasted-over)
      (comp-identification-over
        (identification-over (sE ◁ Vq)
          (change-over r (change-parameter r)
            (IdentificationOver.over (evaluation-compose (g ∘ r) (f ∘ r)))))
        (identification-over (sE ◁ evaluation⁼ δ)
          (change-over r (change-parameter r) (evaluation⁼-over δ))))

  opaque
    left-over : IsIdentificationOver source target left-identification
    left-over = replace-edges₌ (postWhisker pr₁ ◁ left-normalization) (id₌ _)
      (IdentificationOver.over normalized-left-over)

    first-projections-equal : (pr₁ ◁ left-identification) =₂
      (pr₁ ◁ IdentificationOver.identification right)
    first-projections-equal = cancel-left (FunctorOverBase.cell target)
      ((over-to-compatible (IdentificationOver.over right)) ⁻¹ ∙ over-to-compatible left-over)

  private
    module Native = Direct.CompositionRestriction r g f
    module Projection = ProjectedPasting Fq Gq Fp Gp sC sD sE
      (pr₂ {C = P} {D = E}) (pr₂ {C = Q} {D = E}) (uncurry g) (uncurry (g ∘ r))
      (second-projection r) (pair-β₂ pr₁ (uncurry g))
      (pair-β₂ pr₁ (uncurry (g ∘ r))) Eg Ef (uncurry-restrict g r)
    composite-before = FunctorOverBase.functor (evaluation-over (compose g f ∘ r))
    composite-after = FunctorOverBase.functor (evaluation-over (compose (g ∘ r) (f ∘ r)))
    composite-original = FunctorOverBase.functor (evaluation-over (compose g f))
    before-β = pair-β₂ pr₁ (uncurry (compose g f ∘ r))
    after-β = pair-β₂ pr₁ (uncurry (compose (g ∘ r) (f ∘ r)))
    initial-projection = before-β ∙
      restrict-triangle pr₂ sE (second-projection r) composite-before
    changed-projection = after-β ∙
      restrict-triangle pr₂ sE (second-projection r) composite-after
    left-action = Projection.projected-action ∙
      (composition-evaluation (g ∘ r) (f ∘ r) ∙ uncurry⁼ δ)
    right-action = (composition-evaluation g f ▷ sC) ∙ uncurry-restrict (compose g f) r

    opaque
      pasted-projection : SquareCell₌ (pr₂ ◁ pasted) Projection.projected-action
        Projection.source-projection Projection.target-projection
      pasted-projection = Projection.project-paste (ChosenProjections.evaluation-projection r g)

      changed-compose-projection : SquareCell₌ (pr₂ ◁ (sE ◁ Vq))
        (composition-evaluation (g ∘ r) (f ∘ r)) changed-projection Projection.source-projection
      changed-compose-projection = paste-square₌
        (restrict-change-square-One pr₂ sE pr₂ (second-projection r) Vq)
        (composition-projection (g ∘ r) (f ∘ r))

      changed-input-projection : SquareCell₌ (pr₂ ◁ (sE ◁ evaluation⁼ δ))
        (uncurry⁼ δ) initial-projection changed-projection
      changed-input-projection = paste-square₌
        (restrict-change-square-One pr₂ sE pr₂ (second-projection r) (evaluation⁼ δ))
        (pair⁼-triangle₂-One (const (id₌ pr₁)) (uncurry⁼ δ))

      left-projection : SquareCell₌ (pr₂ ◁ left-identification) left-action
        initial-projection Projection.target-projection
      left-projection = replace-edges₌ (postWhisker pr₂ ◁ left-normalization) (id₌ _)
        (lies-over-comp pr₂
          (lies-over-comp pr₂ changed-input-projection changed-compose-projection) pasted-projection)

      right-projection : SquareCell₌ (pr₂ ◁ IdentificationOver.identification right) right-action
        initial-projection Projection.target-projection
      right-projection = lies-over-comp pr₂
        (ChosenProjections.evaluation-projection r (compose g f))
        (restrict-square-One pr₂ Vp (composition-evaluation g f)
          (pair-β₂ pr₁ (uncurry (compose g f)))
          (OverFirstFactor.composite-β₂ P (uncurry g) (uncurry f)) sC
          (composition-projection g f))

      projected-action-inverse : (Native.native-right-change ⁻¹) =₂ Projection.projected-action
      projected-action-inverse =
        let target-assoc = comp-assoc sC Fp (uncurry g)
            inner = uncurry g ◁ Ef
            inner-inverse = uncurry g ◁ Ef ⁻¹
            middle-assoc = comp-assoc Fq sD (uncurry g)
            outer = uncurry-restrict g r ▷ Fq
            inside = inner-inverse ∙ target-assoc
            rest = middle-assoc ⁻¹ ∙ inside
            inverse-inner = inverse-inverse inner ∙ (inv₌ ◁ postWhisker-inverse (uncurry g) Ef)
            expand-inside : (inside ⁻¹) =₂ (target-assoc ⁻¹ ∙ inner)
            expand-inside = comp₌-cong (id₌ (target-assoc ⁻¹)) inverse-inner ∙
              inverse-composite inner-inverse target-assoc
            expand-rest : (rest ⁻¹) =₂ ((target-assoc ⁻¹ ∙ inner) ∙ middle-assoc)
            expand-rest = comp₌-cong expand-inside (inverse-inverse middle-assoc) ∙
              inverse-composite (middle-assoc ⁻¹) inside
            expand-all : (Native.native-right-change ⁻¹) =₂
              (((target-assoc ⁻¹ ∙ inner) ∙ middle-assoc) ∙ outer)
            expand-all = comp₌-cong expand-rest (inverse-inverse outer) ∙
              inverse-composite (outer ⁻¹) rest
        in comp₌-assoc (target-assoc ⁻¹) inner (middle-assoc ∙ outer) ∙
          (comp₌-assoc (target-assoc ⁻¹ ∙ inner) middle-assoc outer ∙ expand-all)

      actions-equal : left-action =₂ right-action
      actions-equal = inv-comp-left Native.native-right-change right-action ∙
        (comp₌-cong (projected-action-inverse ⁻¹) (id₌ (Native.native-right-change ∙ right-action)) ∙
          comp₌-cong (id₌ Projection.projected-action) Native.composition-evaluation-restrict)

  opaque
    second-projections-equal : (pr₂ ◁ left-identification) =₂
      (pr₂ ◁ IdentificationOver.identification right)
    second-projections-equal = cancel-left Projection.target-projection
      (right-projection ⁻¹ ∙ (comp₌-cong actions-equal (id₌ initial-projection) ∙ left-projection))

    composition-restriction : left-identification =₂ IdentificationOver.identification right
    composition-restriction = pair₌-extensionality first-projections-equal second-projections-equal

  left : IdentificationOver {A = One {Γ}} source target
  left = identification-over left-identification left-over

  normalized-change : (sE ∘ composite-after) =₁ (composite-original ∘ sC)
  normalized-change = evaluation-restrict (compose g f) r ∙ (sE ◁ evaluation⁼ δ) ⁻¹

  composite-square : (sE ∘ (Gq ∘ Fq)) =₁ ((Gp ∘ Fp) ∘ sC)
  composite-square = pasted

  opaque
    natural : ((Vp ▷ sC) ∙ normalized-change) =₂ (composite-square ∙ (sE ◁ Vq))
    natural =
      let action = sE ◁ evaluation⁼ δ
          before = Vp ▷ sC
          after = sE ◁ Vq
          output = evaluation-restrict (compose g f) r
          left-normal = comp₌-cong (id₌ before) (inv-comp-right output action) ∙
            comp₌-assoc before normalized-change action
          right-normal = left-normalization ∙ comp₌-assoc pasted after action
      in cancel-right action (right-normal ⁻¹ ∙ (composition-restriction ⁻¹ ∙ left-normal))
```
