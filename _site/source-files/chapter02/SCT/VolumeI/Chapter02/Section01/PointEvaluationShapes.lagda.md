# Point evaluation of shape identifications and identities

A shape identification changes the actual point-insertion square naturally.
For an identity shape, its original closing unitor agrees with the selected
product-functor identity. These are general point-evaluation computations,
used by both endpoints of the degenerate unit triangles.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PointEvaluationShapes where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
  using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition; postWhisker-id₌; preWhisker-id₌; module Boundaries; inv₌)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (const-One; const-pre; comp₌-assoc; comp₌-cong; inv-comp-left; comp-inv-right; inv-comp-right; comp-inv-left; preWhisker-comp₌; interchange-fixedInner; interchange-fixedOuter; interchange; reassociateFour; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (postWhisker-inverse; preWhisker-inverse; comp₌-unitˡ-One; comp₌-unitʳ-One; cancel-left; inverse-inverse; cancel-right)
open import SCT.VolumeI.Chapter01.Section02.Products
  using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (unconst-sides₌; paste-square₌; inverse-square₌; replace-edges₌; post-square₌; identity-square₌; pre-square₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; productMap-id)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong; productMap-cong-triangle₁; productMap-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
  using (product-restriction; restriction-compositor; module ParameterSeparation)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
  using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Functoriality
  using (funPre; funPre-β; funPre-uncurry; funPre-comp)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
  using (evaluate-cong; evaluate⁼-absolute; evaluate-id; evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Currying
  using (funUncurry; funCurry-β; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; insert; identity-family; MorphismFamily; module AtPoint; evAt-cong; evAt-pre)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (preWhisker-comp-One; postWhisker-comp-One; postWhisker-id-One; whisker-mixed-One; left-unitor-comp; right-unitor-comp; triangle-whiskered; pentagon-whiskered-right; identity-unitors)
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors
  using (binary-pre; binary-pre-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
  using (productMap-pair; productMap-pair-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-square; pair₌-unique; pair⁼-comp; pair⁼-cong; pair⁼-id-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One; pair-pre-natural-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares
  using (pair-compatible-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (RestrictionDiagram; Evaluation; restriction-diagram; evaluation)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-square-cell; post-square-cell-id; post-square-cell-comp; restrict-triangle; lies-over-comp; post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change; const-pre-iterated; post-iterated-restriction; post-triangle-comp; post-restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
  using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution
  using (module PairInput; at-pair-input-change; at-pair-restrict)
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution
  using (evaluation-restriction-triangle; evaluate-restrict-inverse-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairingComposition
  using (module NormalizedComposition)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters
  using (module PointNaturality; module UncurryRoute; module ParameterInsertion; module UncurryParameter)

open import SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition using (module InsertionComposition)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair-outer-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairingIdentity using (module ProductPairingIdentity)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (triangle-with-identity)

module ShapeInsertionNaturality {Γ : Context} {P I J : CAT Γ}
  {f g : MAP I J} (alpha : f =₁ g) (a : MAP One I) where
  private
    module Shape = InsertionComposition P
    i : MAP P (P × I)
    i = insert a
    terminal : MAP P One
    terminal = terminate P
    unit = comp-unitˡ (id P)
    first-action = id₌ (id P) ▷ id P
    second-action = alpha ▷ const {P = P} a
    point-action = (alpha ▷ a) ▷ terminal
    before-frame = comp-assoc terminal a f
    after-frame = comp-assoc terminal a g
    before = pair⁼ unit (before-frame ⁻¹)
    after = pair⁼ unit (after-frame ⁻¹)
    top = productMap-cong (id₌ (id P)) alpha ▷ i
    scalar-bottom = pair⁼ (id₌ (id P)) point-action
    native-bottom = pair⁼ (const (id₌ (id P))) point-action
    first-square : (unit ∙ first-action) =₂ (id₌ (id P) ∙ unit)
    first-square = (comp₌-unitˡ-One unit) ⁻¹ ∙
      (comp₌-unitʳ-One unit ∙ comp₌-cong (id₌ unit) (preWhisker-id₌ (id P) (id P)))
    second-square : ((after-frame ⁻¹) ∙ second-action) =₂
      (point-action ∙ (before-frame ⁻¹))
    second-square = inverse-square₌ (preWhisker-comp-One alpha a terminal)
    structural = paste-square₌
      (productMap-pair-outer-One (id₌ (id P)) alpha (id P) (const {P = P} a))
      (pair⁼-square first-square second-square)

  compatibility :
    (Shape.χ g a ∙ (productMap-cong (id₌ (id P)) alpha ▷ insert a)) =₂
    (pair⁼ (const (id₌ (id P))) ((alpha ▷ a) ▷ terminate P) ∙ Shape.χ f a)
  compatibility = replace-edges₌ (id₌ top)
    (pair⁼-cong ((const-One (id₌ (id P))) ⁻¹) (id₌ point-action)) structural

module ShapeEvaluationNaturality {Γ : Context} {I J C : CAT Γ}
  {f g : MAP I J} (alpha : f =₁ g) (a : MAP One I) where
  private
    F : CAT Γ
    F = Fun J C
    e : MAP (F × J) C
    e = funEval
    i : MAP F (F × I)
    i = insert a
    module Shape = InsertionComposition F
    module Native = ShapeInsertionNaturality {P = F} alpha a
    shape-action = productMap-cong (id₌ (id F)) alpha

  compatibility :
    (post-triangle e (productMap (id F) g) i (Shape.χ g a) ∙
      ((e ◁ shape-action) ▷ i)) =₂
    (evAt-cong {C = C} (alpha ▷ a) ∙
      post-triangle e (productMap (id F) f) i (Shape.χ f a))
  compatibility = paste-square₌ (whisker-mixed-One shape-action i e)
    (post-square₌ e Native.compatibility)

module IdentityShapeInsertion {Γ : Context} {P I : CAT Γ} (a : MAP One I) where
  private
    module Shape = InsertionComposition P
    module Structural = ProductPairingIdentity (id P) (const {P = P} a)
    i : MAP P (P × I)
    i = insert a
    terminal-map : MAP P One
    terminal-map = terminate P
    L = comp-unitˡ (id P)
    A = comp-assoc terminal-map a (id I)
    V = comp-unitˡ a ▷ terminal-map
    native-id : id P =₁ id P
    native-id = const {P = One} (id₌ (id P))
    closing = pair⁼ native-id V
    pair-image = productMap-pair (id P) (id I) (id P) (const {P = P} a)
    first-normal : (native-id ∙ L) =₂ L
    first-normal = comp₌-unitˡ-One L ∙ comp₌-cong (const-One (id₌ (id P))) (id₌ L)
    second-normal : (V ∙ (A ⁻¹)) =₂ comp-unitˡ (const {P = P} a)
    second-normal = comp-inv-right (comp-unitˡ (const {P = P} a)) A ∙
      comp₌-cong ((left-unitor-comp terminal-map a) ⁻¹) (id₌ (A ⁻¹))
    pair-normal = pair⁼-cong first-normal second-normal ∙
      ((pair⁼-comp native-id L V (A ⁻¹)) ⁻¹)

  compatibility :
    (closing ∙ Shape.χ (id I) a) =₂
    (comp-unitˡ i ∙ (productMap-id P I ▷ i))
  compatibility = Structural.compatibility ∙
    (comp₌-cong pair-normal (id₌ pair-image) ∙
      ((comp₌-assoc closing (pair⁼ L (A ⁻¹)) pair-image) ⁻¹))

module IdentityShapeEvaluation {Γ : Context} {I C : CAT Γ} (a : MAP One I) where
  private
    F : CAT Γ
    F = Fun I C
    e : MAP (F × I) C
    e = funEval
    i : MAP F (F × I)
    i = insert a
    J : MAP (F × I) (F × I)
    J = productMap (id F) (id I)
    kappa = productMap-id F I
    module Shape = InsertionComposition F
    module Native = IdentityShapeInsertion {P = F} a
    closing = pair⁼ (const (id₌ (id F))) ((comp-unitˡ a) ▷ terminate F)
    chi = Shape.χ (id I) a
    A = comp-assoc i J e
    first = (comp₌-assoc (e ◁ closing) (e ◁ chi) A) ⁻¹
    second = comp₌-cong ((postWhisker-comp₌ e closing chi) ⁻¹) (id₌ A)
    third = comp₌-cong (postWhisker e ◁ Native.compatibility) (id₌ A)
    fourth = (triangle-with-identity e i J kappa) ⁻¹
    fifth = (preWhisker-comp₌ (comp-unitʳ e) (e ◁ kappa) i) ⁻¹

  compatibility :
    (evAt-cong {C = C} (comp-unitˡ a) ∙ post-triangle e J i chi) =₂
    ((comp-unitʳ e ∙ (e ◁ kappa)) ▷ i)
  compatibility = fifth ∙ (fourth ∙ (third ∙ (second ∙ first)))
```
