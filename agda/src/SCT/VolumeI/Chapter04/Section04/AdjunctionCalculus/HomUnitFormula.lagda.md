# The unit formula for the hom equivalence

The hom equivalence of an adjunction is the composite of the functor on
hom categories induced by the right adjoint and precomposition with the
unit. We compare the existing functors through their universal morphism
families, retaining both endpoint frames. In particular, this is a
comparison of functors, not merely a calculation on absolute morphisms.
The family computation first identifies this chosen functor with the
unit-transposition formula for every parameter category.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.HomUnitFormula
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S
  using (hom-reflect; hom-expression-cong)
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition 𝒯 M ℱ P I
  using (hom-image; hom-post-computation)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (IsInvertibleExpression; retarget-invertible; identified-invertible)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (invertible-expression-lift)
open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S
  using (LeftAdjointSection)
import SCT.VolumeI.Chapter02.Section06.HomCompositionEquivalences as Equivalences
import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPoints as Points
import SCT.VolumeI.Chapter02.Section06.HomComposition as Composition
import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomOperations as Operations
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedFamilyTransposition as Sealed
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.HomAdjunctions as HomAdjunctions
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilyFormula as Formula

module AtObjects {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : Obj-abs C) (y : Obj-abs D) where
  private
    module H = HomAdjunctions.HomEquivalence 𝒯 M ℱ P I E S Q adj x y
      using (functor; isEquiv; forward-operation)
    module Realized = Operations.Apply 𝒯 M ℱ P I H.forward-operation
      using (module AtFamily)
    module Unit = Points.AtExpression 𝒯 M ℱ P I (Adjunction.unit-at adj x)
      using (point; family-comparison; normalized; point-comparison)
    module Pre = Composition.At 𝒯 M ℱ P I E S Unit.point
      using (precompose; precompose-β)
    module F = Formula.At.Family 𝒯 M ℱ P I E S adj x y
      (terminate (Hom D (l ∘ x) y)) (hom-expression (id (Hom D (l ∘ x) y)))
      using (comparison)

  functor : MAP (Hom D (l ∘ x) y) (Hom C x (r ∘ y))
  functor = H.functor

  isEquiv : IsEquiv functor
  isEquiv = H.isEquiv

  abstract
    computation : {Γ : CAT} (h : MAP Γ (Hom D (l ∘ x) y)) →
      ExpressionIso (hom-expression (functor ∘ h))
        (Families.Families.forward 𝒯 M ℱ P I E S adj x y (terminate Γ) (hom-expression h))
    computation {Γ} h = expressionIso-compose
      (Sealed.forward-computation 𝒯 M ℱ P I E S Q adj x y (terminate Γ) (hom-expression h))
      (Realized.AtFamily.computation h)

  post : MAP (Hom D (l ∘ x) y) (Hom C (r ∘ (l ∘ x)) (r ∘ y))
  post = hom-post r (l ∘ x) y

  pre : MAP (Hom C (r ∘ (l ∘ x)) (r ∘ y)) (Hom C x (r ∘ y))
  pre = Pre.precompose (r ∘ y)

  private
    Γ : CAT
    Γ = Hom D (l ∘ x) y

    result : MorphismExpression (const {P = Γ} x) (const (r ∘ y))
    result = compose-expression
      (restrict-expression (Adjunction.unit-at adj x) (terminate Γ))
      (hom-image r (hom-expression (id Γ)))

    abstract
      left : ExpressionIso (hom-expression functor) result
      left = expressionIso-compose F.comparison
        (expressionIso-compose (computation (id Γ))
          (hom-expression-cong ((comp-unitʳ functor) ⁻¹)))

      right : ExpressionIso (hom-expression (pre ∘ post)) result
      right = expressionIso-compose
        (compose-expression-cong (Unit.family-comparison Γ)
          (hom-post-computation r (l ∘ x) y))
        (Pre.precompose-β (r ∘ y) post)

  comparison-calculation : functor =₁ (pre ∘ post)
  comparison-calculation = hom-reflect
    {Γ = Γ} {C = C} {x = x} {y = r ∘ y} {h = functor} {k = pre ∘ post}
    (expressionIso-compose {f = hom-expression functor} {g = result}
      {h = hom-expression (pre ∘ post)} (expressionIso-inverse right) left)

  abstract
    comparison : functor =₁ (pre ∘ post)
    comparison = comparison-calculation

    comparison-computation : comparison =₂ comparison-calculation
    comparison-computation = idIso comparison-calculation
```

For an invertible unit, precomposition is an equivalence. Cancelling it
from the existing hom equivalence shows that the right adjoint induces
an equivalence on these hom categories. The final specialization applies
to a left adjoint section and keeps its literal image endpoint.

```agda
  module InvertibleUnit (w : IsInvertibleExpression (Adjunction.unit-at adj x)) where
    private
      point-invertible : IsInvertibleExpression (hom-expression Unit.point)
      point-invertible = identified-invertible (expressionIso-inverse Unit.point-comparison)
        (retarget-invertible (Adjunction.unit-at adj x)
          ((const-One x) ⁻¹) ((const-One (r ∘ (l ∘ x))) ⁻¹) w)
      module Action = Equivalences.InvertiblePoint 𝒯 M ℱ P I E S Q Unit.point
        (invertible-expression-lift (hom-expression Unit.point) point-invertible)
        using (precompose-isEquiv)

    post-isEquiv : IsEquiv post
    post-isEquiv = equiv-cancel-left post pre (Action.precompose-isEquiv (r ∘ y))
      (equiv-transport comparison H.isEquiv)

module LeftSection {C D : CAT} {p : MAP C D} {s : MAP D C}
  (w : LeftAdjointSection p s) (x : Obj-abs D) (y : Obj-abs C) where
  private
    module A = LeftAdjointSection w using (adjunction; unit-at-invertible)
    module UnitFormula = AtObjects A.adjunction x y using (module InvertibleUnit)

  hom-post-isEquiv : IsEquiv (hom-post p (s ∘ x) y)
  hom-post-isEquiv = UnitFormula.InvertibleUnit.post-isEquiv (A.unit-at-invertible x)
```
