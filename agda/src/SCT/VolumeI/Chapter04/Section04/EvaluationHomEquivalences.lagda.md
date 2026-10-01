# Homs to and from identity arrows

Target evaluation identifies morphisms from an arrow to an identity arrow
with morphisms out of its target. Source evaluation gives the dual assertion.
These equivalences follow from the evaluation adjoint sections and the unit
and counit formulas. Composition with the hom points of the endpoint isomorphisms normalizes
evaluation of an identity arrow. The raw evaluation functors remain visible,
and the normalization uses the existing hom-composition operations.
The universal framed square identifies source evaluation with precomposition
by the original arrow.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.EvaluationHomEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section04.EvaluationAdjunctions 𝒯 M ℱ P I E S Q R
  using (source-evaluation-left-adjoint-section; target-evaluation-right-adjoint-section)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.HomUnitFormula as Units
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.HomCounitFormula as Counits
import SCT.VolumeI.Chapter02.Section06.HomComposition as Composition
import SCT.VolumeI.Chapter02.Section06.HomCompositionEquivalences as CompositionEquivalences
import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPoints as Points
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-id; expressionIso-compose; expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (IsInvertibleExpression; retarget-invertible; identified-invertible)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.PrimitiveInverses 𝒯 M ℱ P I E S
  using (identification-invertible)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (invertible-expression-lift)

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S
  using (hom-reflect)
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition 𝒯 M ℱ P I
  using (hom-image; hom-post-computation)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-restrict)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionWithIdentifications 𝒯 M ℱ P I E S
  using (postcompose-identification)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (right-unit)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I using (constant-frame)
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.ArrowCategorySquares 𝒯 M ℱ P I E S
  using (FramedSquare)
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.FramedSquareCommutativity as Square
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantIdentityComparison as Identity
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction

private
  module IdentificationPoint {C : CAT} {x y : Obj-abs C} (κ : x =₁ y) where
    module Point = Points.AtExpression 𝒯 M ℱ P I (isomorphism-expression κ)
      using (point; point-comparison; family-comparison)
    abstract
      invertible : IsInvertibleExpression (hom-expression Point.point)
      invertible = identified-invertible (expressionIso-inverse Point.point-comparison)
        (retarget-invertible (isomorphism-expression κ)
          ((const-One x) ⁻¹) ((const-One y) ⁻¹) (identification-invertible κ))
    module Equivalences = CompositionEquivalences.InvertiblePoint 𝒯 M ℱ P I E S Q Point.point
      (invertible-expression-lift (hom-expression Point.point) invertible)
      using (precompose-isEquiv; postcompose-isEquiv)


module NormalizedEvaluation {C : CAT} (a : Obj-abs (Ar C)) (z : Obj-abs C)
  (v : MAP (Ar C) C) (boundary : (v ∘ identityArrow) =₁ id C) where
  Γ = Hom (Ar C) a (identityArrow ∘ z)
  raw : MAP Γ (Hom C (v ∘ a) (v ∘ (identityArrow ∘ z)))
  raw = hom-post v a (identityArrow ∘ z)
  frame : (v ∘ (identityArrow ∘ z)) =₁ z
  frame = constant-frame v boundary z
  private
    module Correction = IdentificationPoint frame using (module Point; module Equivalences)
    module Compose = Composition.At 𝒯 M ℱ P I E S Correction.Point.point
      using (postcompose; postcompose-β)
  functor : MAP Γ (Hom C (v ∘ a) z)
  functor = Compose.postcompose (v ∘ a) ∘ raw
  isEquiv : IsEquiv raw → IsEquiv functor
  isEquiv e = equiv-compose raw (Compose.postcompose (v ∘ a)) e
    (Correction.Equivalences.postcompose-isEquiv (v ∘ a))

  private
    t = terminate Γ
    V = hom-expression (id Γ)
    cx = constant-image Γ v a
    cy = constant-image Γ v (identityArrow ∘ z)
  evaluated : MorphismExpression (const {P = Γ} (v ∘ a)) (const z)
  evaluated = retarget-expression (post-expression v V)
    ((idIso (v ∘ a) ▷ t) ∙ cx) ((frame ▷ t) ∙ cy)

  abstract
    computation : ExpressionIso (hom-expression functor) evaluated
    computation = expressionIso-compose
      (retarget-cong (post-expression v V)
        (isoComp-cong ((preWhisker-idIso (v ∘ a) t) ⁻¹) (idIso cx))
        (idIso ((frame ▷ t) ∙ cy)))
      (expressionIso-compose
        (retarget-assoc (post-expression v V) cx cy (idIso (const (v ∘ a))) (frame ▷ t))
        (expressionIso-compose
          (postcompose-identification (hom-image v V) (frame ▷ t))
          (expressionIso-compose
            (compose-expression-cong (hom-post-computation v a (identityArrow ∘ z))
              (expressionIso-compose (isomorphism-restrict frame t) (Correction.Point.family-comparison Γ)))
            (Compose.postcompose-β (v ∘ a) raw))))

module ToIdentity {C : CAT} (a : Obj-abs (Ar C)) (z : Obj-abs C) where
  private
    module Source = NormalizedEvaluation a z ev₀ identity-source
      using (functor; evaluated; computation)
    module Target = NormalizedEvaluation a z ev₁ identity-target
      using (raw; functor; isEquiv; evaluated; computation)
  raw : MAP (Hom (Ar C) a (identityArrow ∘ z))
    (Hom C (ev₁ ∘ a) (ev₁ ∘ (identityArrow ∘ z)))
  raw = Target.raw
  raw-isEquiv : IsEquiv raw
  raw-isEquiv = Counits.RightSection.hom-post-isEquiv 𝒯 M ℱ P I E S Q
    (target-evaluation-right-adjoint-section C) a z
  functor : MAP (Hom (Ar C) a (identityArrow ∘ z)) (Hom C (ev₁ ∘ a) z)
  functor = Target.functor
  isEquiv : IsEquiv functor
  isEquiv = Target.isEquiv raw-isEquiv
  source-functor : MAP (Hom (Ar C) a (identityArrow ∘ z)) (Hom C (ev₀ ∘ a) z)
  source-functor = Source.functor

  arrow : MorphismExpression (ev₀ ∘ a) (ev₁ ∘ a)
  arrow = record { arrow = a ; source-frame = idIso (ev₀ ∘ a) ; target-frame = idIso (ev₁ ∘ a) }
  private
    Γ = Hom (Ar C) a (identityArrow ∘ z)
    t = terminate Γ
    module ArrowPoint = Points.AtExpression 𝒯 M ℱ P I arrow using (point; family-comparison)
    module Pre = Composition.At 𝒯 M ℱ P I E S ArrowPoint.point using (precompose; precompose-β)
    J : MorphismExpression z z
    J = record { arrow = identityArrow ∘ z
      ; source-frame = constant-frame ev₀ identity-source z
      ; target-frame = constant-frame ev₁ identity-target z }
    L = restrict-expression arrow t
    R′ = restrict-expression J t
    top = Source.evaluated
    bottom = Target.evaluated
    square : FramedSquare top R′ L bottom
    square = record { vertical = hom-expression (id Γ)
      ; top-edge = expressionIso-id top ; bottom-edge = expressionIso-id bottom }
    module Commutativity = Square.At 𝒯 M ℱ P I E S square using (comparison)
    abstract
      identity-side : ExpressionIso R′ (identity-expression (const z))
      identity-side = expressionIso-compose (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E z t)
        (restrict-expressionIso (Identity.At.comparison 𝒯 M ℱ P I E z) t)
      relation : ExpressionIso top (compose-expression L bottom)
      relation = expressionIso-compose Commutativity.comparison
        (expressionIso-compose
          (compose-expression-cong (expressionIso-id top) (expressionIso-inverse identity-side))
          (expressionIso-inverse (right-unit top)))
      left : ExpressionIso (hom-expression source-functor) (compose-expression L bottom)
      left = expressionIso-compose relation Source.computation
      right : ExpressionIso (hom-expression (Pre.precompose z ∘ functor)) (compose-expression L bottom)
      right = expressionIso-compose
        (compose-expression-cong (ArrowPoint.family-comparison Γ) Target.computation)
        (Pre.precompose-β z functor)

  point : Obj-abs (Hom C (ev₀ ∘ a) (ev₁ ∘ a))
  point = ArrowPoint.point
  precompose : MAP (Hom C (ev₁ ∘ a) z) (Hom C (ev₀ ∘ a) z)
  precompose = Pre.precompose z
  source-comparison-calculation : source-functor =₁ (precompose ∘ functor)
  source-comparison-calculation = hom-reflect
    {Γ = Γ} {C = C} {x = ev₀ ∘ a} {y = z} {h = source-functor} {k = precompose ∘ functor}
    (expressionIso-compose (expressionIso-inverse right) left)
  abstract
    source-comparison : source-functor =₁ (precompose ∘ functor)
    source-comparison = source-comparison-calculation
    source-comparison-computation : source-comparison =₂ source-comparison-calculation
    source-comparison-computation = idIso source-comparison-calculation

module FromIdentity {C : CAT} (z : Obj-abs C) (a : Obj-abs (Ar C)) where
  raw : MAP (Hom (Ar C) (identityArrow ∘ z) a)
    (Hom C (ev₀ ∘ (identityArrow ∘ z)) (ev₀ ∘ a))
  raw = hom-post ev₀ (identityArrow ∘ z) a

  raw-isEquiv : IsEquiv raw
  raw-isEquiv = Units.LeftSection.hom-post-isEquiv 𝒯 M ℱ P I E S Q
    (source-evaluation-left-adjoint-section C) z a

  source-frame : (ev₀ ∘ (identityArrow ∘ z)) =₁ z
  source-frame = comp-unitˡ z ∙
    ((identity-source ▷ z) ∙ (comp-assoc z identityArrow ev₀) ⁻¹)

  private
    module Correction = IdentificationPoint (source-frame ⁻¹)
      using (module Point; module Equivalences)
    module Compose = Composition.At 𝒯 M ℱ P I E S Correction.Point.point
      using (precompose; precompose-β)

  functor : MAP (Hom (Ar C) (identityArrow ∘ z) a) (Hom C z (ev₀ ∘ a))
  functor = Compose.precompose (ev₀ ∘ a) ∘ raw

  isEquiv : IsEquiv functor
  isEquiv = equiv-compose raw (Compose.precompose (ev₀ ∘ a)) raw-isEquiv
    (Correction.Equivalences.precompose-isEquiv (ev₀ ∘ a))
```
