# Expanded components and changes of parameters

The expanded composite unit and counit respect identifications of their
parameters. Their triangle equations are transported from the opaque
calculation to the underlying framed expression operations.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeExpandedComponents
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeTriangleAlgebra as Algebra
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeFormulas as Formulas

module At {Γ C D T : CAT} {l : MAP C D} {r : MAP D C}
  {k : MAP D T} {s : MAP T D} (adjA : Adjunction l r) (adjB : Adjunction k s) where
  module A = Adjunction adjA using (unit-at; counit-at)
  module B = Adjunction adjB using (unit-at; counit-at)
  module AR = Restriction.Components 𝒯 M ℱ P I E S adjA using (unit-parameter; counit-parameter)
  module BR = Restriction.Components 𝒯 M ℱ P I E S adjB using (unit-parameter; counit-parameter)
  module X = Algebra.At.X 𝒯 M ℱ P I E S Q Γ
  module K = X.K
  module Core = Algebra.At.Composite 𝒯 M ℱ P I E S Q Γ adjA adjB
  private module Formula = Formulas.At.Composite 𝒯 M ℱ P I E S Q Γ adjA adjB using (raw-unit; raw-counit; unit-comparison; counit-comparison)

  expanded-unit : (x : MAP Γ C) → MorphismExpression x (r ∘ (s ∘ (k ∘ (l ∘ x))))
  expanded-unit = Formula.raw-unit

  expanded-counit : (y : MAP Γ T) → MorphismExpression (k ∘ (l ∘ (r ∘ (s ∘ y)))) y
  expanded-counit = Formula.raw-counit

  abstract
    unit-comparison : (x : MAP Γ C) → ExpressionIso (expanded-unit x) (Core.expanded-unit x)
    unit-comparison = Formula.unit-comparison

    counit-comparison : (y : MAP Γ T) → ExpressionIso (expanded-counit y) (Core.expanded-counit y)
    counit-comparison = Formula.counit-comparison

    unit-parameter : {x x′ : MAP Γ C} (ξ : x =₁ x′) →
      ExpressionIso (retarget-expression (expanded-unit x) ξ (r ◁ (s ◁ (k ◁ (l ◁ ξ)))))
        (expanded-unit x′)
    unit-parameter {x} {x′} ξ = expressionIso-compose
      (compose-expression-cong (AR.unit-parameter ξ)
        (expressionIso-compose (post-expressionIso r (BR.unit-parameter (l ◁ ξ)))
          (expressionIso-inverse (post-retarget r (B.unit-at (l ∘ x)) (l ◁ ξ) (s ◁ (k ◁ (l ◁ ξ)))))))
      (expressionIso-inverse (retarget-composition (A.unit-at x) (post-expression r (B.unit-at (l ∘ x)))
        ξ (r ◁ (l ◁ ξ)) (r ◁ (s ◁ (k ◁ (l ◁ ξ))))))

    counit-parameter : {y y′ : MAP Γ T} (ξ : y =₁ y′) →
      ExpressionIso (retarget-expression (expanded-counit y) (k ◁ (l ◁ (r ◁ (s ◁ ξ)))) ξ)
        (expanded-counit y′)
    counit-parameter {y} {y′} ξ = expressionIso-compose
      (compose-expression-cong
        (expressionIso-compose (post-expressionIso k (AR.counit-parameter (s ◁ ξ)))
          (expressionIso-inverse (post-retarget k (A.counit-at (s ∘ y)) (l ◁ (r ◁ (s ◁ ξ))) (s ◁ ξ))))
        (BR.counit-parameter ξ))
      (expressionIso-inverse (retarget-composition (post-expression k (A.counit-at (s ∘ y))) (B.counit-at y)
        (k ◁ (l ◁ (r ◁ (s ◁ ξ)))) (k ◁ (s ◁ ξ)) ξ))

    left-triangle : (x : MAP Γ C) →
      ExpressionIso (compose-expression (post-expression k (post-expression l (expanded-unit x)))
        (expanded-counit (k ∘ (l ∘ x)))) (identity-expression (k ∘ (l ∘ x)))
    left-triangle x = expressionIso-compose (K.identity-comparison (k ∘ (l ∘ x)))
      (expressionIso-compose (Core.left-triangle x)
        (expressionIso-compose
          (expressionIso-inverse (K.composite-comparison
            (K.post k (K.post l (Core.expanded-unit x))) (Core.expanded-counit (k ∘ (l ∘ x)))))
          (compose-expression-cong
            (expressionIso-compose (expressionIso-inverse (X.double-post-comparison l k (Core.expanded-unit x)))
              (post-expressionIso k (post-expressionIso l (unit-comparison x))))
            (counit-comparison (k ∘ (l ∘ x))))))

    right-triangle : (y : MAP Γ T) →
      ExpressionIso (compose-expression (expanded-unit (r ∘ (s ∘ y)))
        (post-expression r (post-expression s (expanded-counit y)))) (identity-expression (r ∘ (s ∘ y)))
    right-triangle y = expressionIso-compose (K.identity-comparison (r ∘ (s ∘ y)))
      (expressionIso-compose (Core.right-triangle y)
        (expressionIso-compose
          (expressionIso-inverse (K.composite-comparison
            (Core.expanded-unit (r ∘ (s ∘ y))) (K.post r (K.post s (Core.expanded-counit y)))))
          (compose-expression-cong (unit-comparison (r ∘ (s ∘ y)))
            (expressionIso-compose (expressionIso-inverse (X.double-post-comparison s r (Core.expanded-counit y)))
              (post-expressionIso r (post-expressionIso s (counit-comparison y)))))))
```
