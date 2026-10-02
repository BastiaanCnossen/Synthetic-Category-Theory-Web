# Formulas for the components of a composite adjunction

The expanded unit and counit can be written with their raw constructions
or with the chosen opaque operations. These comparisons connect
the two formulas before any composite triangle identity is proved. Both the
component calculations and the triangle arguments use these same formulas.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeFormulas
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionOperations as Operations

module At (Γ : CAT) where
  module K = Operations.ExpressionOperations (Operations.expression-operations 𝒯 M ℱ P I E S Γ)

  module Composite {C D T : CAT} {l : MAP C D} {r : MAP D C}
    {k : MAP D T} {s : MAP T D} (adjA : Adjunction l r) (adjB : Adjunction k s) where
    private
      module A = Adjunction adjA using (unit-at; counit-at)
      module B = Adjunction adjB using (unit-at; counit-at)

    raw-unit : (x : MAP Γ C) → MorphismExpression x (r ∘ (s ∘ (k ∘ (l ∘ x))))
    raw-unit x = compose-expression (A.unit-at x) (post-expression r (B.unit-at (l ∘ x)))

    raw-counit : (y : MAP Γ T) → MorphismExpression (k ∘ (l ∘ (r ∘ (s ∘ y)))) y
    raw-counit y = compose-expression (post-expression k (A.counit-at (s ∘ y))) (B.counit-at y)

    expanded-unit : (x : MAP Γ C) → MorphismExpression x (r ∘ (s ∘ (k ∘ (l ∘ x))))
    expanded-unit x = K.composite (A.unit-at x) (K.post r (B.unit-at (l ∘ x)))

    expanded-counit : (y : MAP Γ T) → MorphismExpression (k ∘ (l ∘ (r ∘ (s ∘ y)))) y
    expanded-counit y = K.composite (K.post k (A.counit-at (s ∘ y))) (B.counit-at y)

    abstract
      unit-comparison : (x : MAP Γ C) → ExpressionIso (raw-unit x) (expanded-unit x)
      unit-comparison x = expressionIso-inverse (expressionIso-compose
        (compose-expression-cong (expressionIso-id (A.unit-at x)) (K.post-comparison r (B.unit-at (l ∘ x))))
        (K.composite-comparison (A.unit-at x) (K.post r (B.unit-at (l ∘ x)))))

      counit-comparison : (y : MAP Γ T) → ExpressionIso (raw-counit y) (expanded-counit y)
      counit-comparison y = expressionIso-inverse (expressionIso-compose
        (compose-expression-cong (K.post-comparison k (A.counit-at (s ∘ y))) (expressionIso-id (B.counit-at y)))
        (K.composite-comparison (K.post k (A.counit-at (s ∘ y))) (B.counit-at y)))
```
