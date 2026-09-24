# Associativity with specified endpoints

Glue each composite triangle to a unit triangle, then compose the two
resulting squares in the arrow category. Their outside square compares
the two bracketings after adding identity edges. The proved unit laws
remove those edges. Every comparison below preserves both endpoint frames.

The notation `compose-expression f g` follows `f` and then `g`. Thus
`associativity` compares `(h ∘ g) ∘ f` with `h ∘ (g ∘ f)`.

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

module SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.ArrowCategorySquares 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)
open import SCT.VolumeI.Chapter02.Section02.PresentationComparisons 𝒯 M ℱ P I E S using (change-long)
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.GlobalCompositionExpressions 𝒯 M ℱ P I E S
  using (global-compose-expression; global-composition-comparison)
import SCT.VolumeI.Chapter02.Section02.GluedFramedSquares as Gluing
import SCT.VolumeI.Chapter02.Section02.FramedSquareCommutativity as Commutativity

module At {Γ C : CAT} {x y z w : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) (h : MorphismExpression z w) where
  fg = compose-expression f g
  gh = compose-expression g h
  module First = Gluing.At 𝒯 M ℱ P I E S Q (composition-presentation f g)
    (change-long (composition-presentation (identity-expression x) fg) (left-unit fg))
  module Second = Gluing.At 𝒯 M ℱ P I E S Q
    (change-long (composition-presentation gh (identity-expression w)) (right-unit gh))
    (composition-presentation g h)
  module Outside = Compose First.square Second.square

  comparison : ExpressionIso (compose-expression f gh) (compose-expression fg h)
  comparison = expressionIso-compose (left-unit (compose-expression fg h))
    (expressionIso-compose (Commutativity.At.comparison 𝒯 M ℱ P I E S Outside.square)
      (expressionIso-inverse (right-unit (compose-expression f gh))))

associativity : {Γ C : CAT} {x y z w : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) (h : MorphismExpression z w) →
  ExpressionIso (compose-expression f (compose-expression g h))
    (compose-expression (compose-expression f g) h)
associativity = At.comparison

global-associativity : {Γ C : CAT} {x y z w : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) (h : MorphismExpression z w) →
  ExpressionIso (global-compose-expression f (global-compose-expression g h))
    (global-compose-expression (global-compose-expression f g) h)
global-associativity f g h = expressionIso-compose
  (expressionIso-inverse (expressionIso-compose
    (compose-expression-cong (global-composition-comparison f g) (expressionIso-id h))
    (global-composition-comparison (global-compose-expression f g) h)))
  (expressionIso-compose (associativity f g h)
    (expressionIso-compose
      (compose-expression-cong (expressionIso-id f) (global-composition-comparison g h))
      (global-composition-comparison f (global-compose-expression g h))))
```
