# Component laws in the opaque expression calculus

The component naturality and triangle equations of an adjunction are
transported to the checked expression calculus. This keeps subsequent
composition calculations from expanding the underlying Segal constructions.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedComponents
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionCalculus 𝒯 M ℱ P I E S Q
  using (ExpressionCalculus; expression-calculus)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentNaturality as Naturality
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentTriangles as Triangles

module At (Γ : CAT) where
  module K = ExpressionCalculus (expression-calculus Γ)

  abstract
    post-cong : {C D : CAT} (F : MAP C D) {x y : MAP Γ C}
      {u v : MorphismExpression x y} → ExpressionIso u v → ExpressionIso (K.post F u) (K.post F v)
    post-cong F {u = u} {v} same = expressionIso-compose (expressionIso-inverse (K.post-comparison F v))
      (expressionIso-compose (post-expressionIso F same) (K.post-comparison F u))

    double-post-comparison : {B C D : CAT} (F : MAP B C) (G : MAP C D)
      {x y : MAP Γ B} (u : MorphismExpression x y) →
      ExpressionIso (K.post G (K.post F u)) (post-expression G (post-expression F u))
    double-post-comparison F G u = expressionIso-compose (post-expressionIso G (K.post-comparison F u))
      (K.post-comparison G (K.post F u))

  module Components {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) where
    module A = Adjunction adj using (unit-at; counit-at)
    module N = Naturality.Components 𝒯 M ℱ P I E S adj using (unit-natural; counit-natural)
    module T = Triangles.Components 𝒯 M ℱ P I E S adj using (left-triangle-at; right-triangle-at)

    abstract
      unit-natural : {x y : MAP Γ C} (u : MorphismExpression x y) →
        ExpressionIso (K.composite (A.unit-at x) (K.post r (K.post l u)))
          (K.composite u (A.unit-at y))
      unit-natural {x} {y} u = expressionIso-compose (expressionIso-inverse (K.composite-comparison u (A.unit-at y)))
        (expressionIso-compose (N.unit-natural u)
          (expressionIso-compose (compose-expression-cong (expressionIso-id (A.unit-at x)) (double-post-comparison l r u))
            (K.composite-comparison (A.unit-at x) (K.post r (K.post l u)))))

      counit-natural : {x y : MAP Γ D} (u : MorphismExpression x y) →
        ExpressionIso (K.composite (K.post l (K.post r u)) (A.counit-at y))
          (K.composite (A.counit-at x) u)
      counit-natural {x} {y} u = expressionIso-compose (expressionIso-inverse (K.composite-comparison (A.counit-at x) u))
        (expressionIso-compose (N.counit-natural u)
          (expressionIso-compose (compose-expression-cong (double-post-comparison r l u) (expressionIso-id (A.counit-at y)))
            (K.composite-comparison (K.post l (K.post r u)) (A.counit-at y))))

      left-triangle : (x : MAP Γ C) →
        ExpressionIso (K.composite (K.post l (A.unit-at x)) (A.counit-at (l ∘ x)))
          (K.identity (l ∘ x))
      left-triangle x = expressionIso-compose (expressionIso-inverse (K.identity-comparison (l ∘ x)))
        (expressionIso-compose (T.left-triangle-at x) (K.action-comparison l (A.unit-at x) (A.counit-at (l ∘ x))))

      right-triangle : (y : MAP Γ D) →
        ExpressionIso (K.composite (A.unit-at (r ∘ y)) (K.post r (A.counit-at y)))
          (K.identity (r ∘ y))
      right-triangle y = expressionIso-compose (expressionIso-inverse (K.identity-comparison (r ∘ y)))
        (expressionIso-compose (T.right-triangle-at y)
          (expressionIso-compose (compose-expression-cong (expressionIso-id (A.unit-at (r ∘ y))) (K.post-comparison r (A.counit-at y)))
            (K.composite-comparison (A.unit-at (r ∘ y)) (K.post r (A.counit-at y)))))
```
