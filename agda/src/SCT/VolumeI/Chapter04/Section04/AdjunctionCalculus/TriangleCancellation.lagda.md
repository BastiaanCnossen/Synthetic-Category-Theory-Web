# Cancellation of a naturality square by a triangle

These two elementary calculations isolate the algebra in the inverse
transposition laws. All expressions are arbitrary, and the displayed
naturality and triangle comparisons are hypotheses of the lemmas. The
application to an adjunction supplies these hypotheses by the separately
proved component laws.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TriangleCancellation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.ExpressionCancellation 𝒯 M ℱ P I E S Q public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity 𝒯 M ℱ P I E S Q
  using (associativity)

abstract
  post-cancel : {Γ C D : CAT} (F : MAP C D) {x y z : MAP Γ C} {w : MAP Γ D}
    (u : MorphismExpression x y) (v : MorphismExpression y z)
    (h : MorphismExpression (F ∘ z) w) (e : MorphismExpression (F ∘ y) (F ∘ x))
    (α : MorphismExpression (F ∘ x) w) →
    ExpressionIso (compose-expression (post-expression F v) h) (compose-expression e α) →
    ExpressionIso (compose-expression (post-expression F u) e) (identity-expression (F ∘ x)) →
    ExpressionIso (compose-expression (post-expression F (compose-expression u v)) h) α
  post-cancel F u v h e α natural triangle =
    expressionIso-compose (InverseEquation.cancel-before (post-expression F u) e triangle α)
      (expressionIso-compose (compose-expression-cong (expressionIso-id (post-expression F u)) natural)
        (expressionIso-compose
          (expressionIso-inverse (associativity (post-expression F u) (post-expression F v) h))
          (compose-expression-cong (expressionIso-inverse (post-composition F u v)) (expressionIso-id h))))

  pre-cancel : {Γ C D : CAT} (F : MAP C D) {x y z : MAP Γ C} {w : MAP Γ D}
    (u : MorphismExpression x y) (v : MorphismExpression y z)
    (f : MorphismExpression w (F ∘ x)) (β : MorphismExpression w (F ∘ z))
    (e : MorphismExpression (F ∘ z) (F ∘ y)) →
    ExpressionIso (compose-expression f (post-expression F u)) (compose-expression β e) →
    ExpressionIso (compose-expression e (post-expression F v)) (identity-expression (F ∘ z)) →
    ExpressionIso (compose-expression f (post-expression F (compose-expression u v))) β
  pre-cancel F u v f β e natural triangle =
    expressionIso-compose (InverseEquation.cancel-after e (post-expression F v) triangle β)
      (expressionIso-compose (compose-expression-cong natural (expressionIso-id (post-expression F v)))
        (expressionIso-compose (associativity f (post-expression F u) (post-expression F v))
          (compose-expression-cong (expressionIso-id f) (expressionIso-inverse (post-composition F u v)))))
```
