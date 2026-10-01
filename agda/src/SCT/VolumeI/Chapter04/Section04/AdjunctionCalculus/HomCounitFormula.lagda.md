# The counit formula for the inverse hom equivalence

The inverse of the existing adjunction hom equivalence is induced by the
left adjoint followed by postcomposition with the counit. The comparison
is between functors and retains both endpoint frames for arbitrary families.
When the counit is invertible, cancelling its postcomposition shows that
the left adjoint induces an equivalence on these hom categories.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.HomCounitFormula
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
  using (RightAdjointSection)
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
      using (isEquiv; backward-operation)
    module Realized = Operations.Apply 𝒯 M ℱ P I H.backward-operation
      using (functor; module AtFamily)
    module Counit = Points.AtExpression 𝒯 M ℱ P I (Adjunction.counit-at adj y)
      using (point; family-comparison; point-comparison)
    module Post = Composition.At 𝒯 M ℱ P I E S Counit.point
      using (postcompose; postcompose-β)
    module F = Formula.At.BackwardFamily 𝒯 M ℱ P I E S adj x y
      (terminate (Hom C x (r ∘ y))) (hom-expression (id (Hom C x (r ∘ y))))
      using (comparison)

  functor : MAP (Hom C x (r ∘ y)) (Hom D (l ∘ x) y)
  functor = Realized.functor

  isEquiv : IsEquiv functor
  isEquiv = equiv-inverse H.isEquiv

  abstract
    computation : {Γ : CAT} (h : MAP Γ (Hom C x (r ∘ y))) →
      ExpressionIso (hom-expression (functor ∘ h))
        (Families.Families.backward 𝒯 M ℱ P I E S adj x y (terminate Γ) (hom-expression h))
    computation {Γ} h = expressionIso-compose
      (Sealed.backward-computation 𝒯 M ℱ P I E S Q adj x y (terminate Γ) (hom-expression h))
      (Realized.AtFamily.computation h)

  post : MAP (Hom C x (r ∘ y)) (Hom D (l ∘ x) (l ∘ (r ∘ y)))
  post = hom-post l x (r ∘ y)

  compose-counit : MAP (Hom D (l ∘ x) (l ∘ (r ∘ y))) (Hom D (l ∘ x) y)
  compose-counit = Post.postcompose (l ∘ x)

  private
    Γ : CAT
    Γ = Hom C x (r ∘ y)

    result : MorphismExpression (const {P = Γ} (l ∘ x)) (const y)
    result = compose-expression
      (hom-image l (hom-expression (id Γ)))
      (restrict-expression (Adjunction.counit-at adj y) (terminate Γ))

    abstract
      left : ExpressionIso (hom-expression functor) result
      left = expressionIso-compose F.comparison
        (expressionIso-compose (computation (id Γ))
          (hom-expression-cong ((comp-unitʳ functor) ⁻¹)))

      right : ExpressionIso (hom-expression (compose-counit ∘ post)) result
      right = expressionIso-compose
        (compose-expression-cong (hom-post-computation l x (r ∘ y))
          (Counit.family-comparison Γ))
        (Post.postcompose-β (l ∘ x) post)

  comparison-calculation : functor =₁ (compose-counit ∘ post)
  comparison-calculation = hom-reflect
    {Γ = Γ} {C = D} {x = l ∘ x} {y = y} {h = functor} {k = compose-counit ∘ post}
    (expressionIso-compose {f = hom-expression functor} {g = result}
      {h = hom-expression (compose-counit ∘ post)} (expressionIso-inverse right) left)

  abstract
    comparison : functor =₁ (compose-counit ∘ post)
    comparison = comparison-calculation

    comparison-computation : comparison =₂ comparison-calculation
    comparison-computation = idIso comparison-calculation

  module InvertibleCounit (w : IsInvertibleExpression (Adjunction.counit-at adj y)) where
    private
      point-invertible : IsInvertibleExpression (hom-expression Counit.point)
      point-invertible = identified-invertible (expressionIso-inverse Counit.point-comparison)
        (retarget-invertible (Adjunction.counit-at adj y)
          ((const-One (l ∘ (r ∘ y))) ⁻¹) ((const-One y) ⁻¹) w)
      module Action = Equivalences.InvertiblePoint 𝒯 M ℱ P I E S Q Counit.point
        (invertible-expression-lift (hom-expression Counit.point) point-invertible)
        using (postcompose-isEquiv)

    post-isEquiv : IsEquiv post
    post-isEquiv = equiv-cancel-left post compose-counit (Action.postcompose-isEquiv (l ∘ x))
      (equiv-transport comparison isEquiv)
```

For a right adjoint section, the result keeps the literal endpoint p(s y).
No strict equality between that endpoint and y is assumed.

```agda
module RightSection {C D : CAT} {p : MAP C D} {s : MAP D C}
  (w : RightAdjointSection p s) (x : Obj-abs C) (y : Obj-abs D) where
  private
    module A = RightAdjointSection w using (adjunction; counit-at-invertible)
    module CounitFormula = AtObjects A.adjunction x y using (module InvertibleCounit)

  hom-post-isEquiv : IsEquiv (hom-post p x (s ∘ y))
  hom-post-isEquiv = CounitFormula.InvertibleCounit.post-isEquiv (A.counit-at-invertible y)
```
