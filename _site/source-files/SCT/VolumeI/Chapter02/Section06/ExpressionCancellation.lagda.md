# Cancellation by an inverse morphism

Associativity and the unit laws turn one inverse equation into cancellation
on either side. All comparisons retain their specified endpoints.

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

module SCT.VolumeI.Chapter02.Section06.ExpressionCancellation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.CompositionExpressions 𝒯 M ℱ P I E S public using (compose-expression)
open import SCT.VolumeI.Chapter02.Section02.CompositionIdentifications 𝒯 M ℱ P I E S public using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)
open import SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity 𝒯 M ℱ P I E S Q using (associativity)

module InverseEquation {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y x)
  (law : ExpressionIso (compose-expression f g) (identity-expression x)) where

  cancel-after : {z : MAP Γ C} (h : MorphismExpression z x) →
    ExpressionIso (compose-expression (compose-expression h f) g) h
  cancel-after h = expressionIso-compose (right-unit h)
    (expressionIso-compose (compose-expression-cong (expressionIso-id h) law)
      (expressionIso-inverse (associativity h f g)))

  cancel-before : {z : MAP Γ C} (h : MorphismExpression x z) →
    ExpressionIso (compose-expression f (compose-expression g h)) h
  cancel-before h = expressionIso-compose (left-unit h)
    (expressionIso-compose (compose-expression-cong law (expressionIso-id h)) (associativity f g h))

  reflect-after : {z : MAP Γ C} (h k : MorphismExpression z x) →
    ExpressionIso (compose-expression h f) (compose-expression k f) → ExpressionIso h k
  reflect-after h k α = expressionIso-compose (cancel-after k)
    (expressionIso-compose (compose-expression-cong α (expressionIso-id g)) (expressionIso-inverse (cancel-after h)))

  reflect-before : {z : MAP Γ C} (h k : MorphismExpression x z) →
    ExpressionIso (compose-expression g h) (compose-expression g k) → ExpressionIso h k
  reflect-before h k α = expressionIso-compose (cancel-before k)
    (expressionIso-compose (compose-expression-cong (expressionIso-id f) α) (expressionIso-inverse (cancel-before h)))
```
