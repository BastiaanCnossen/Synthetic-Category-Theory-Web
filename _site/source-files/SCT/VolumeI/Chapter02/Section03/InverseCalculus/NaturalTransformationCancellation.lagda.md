# Cancelling an invertible component in a naturality square

Naturality transfers a comparison between the images of two morphisms
under one functor to a comparison under the other. An invertible source
component gives one direction, and an invertible target component gives
the other. The proof works uniformly over an arbitrary absolute parameter
category and retains both endpoint equations.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.NaturalTransformationCancellation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.ExpressionCancellation 𝒯 M ℱ P I E S Q
  using (module InverseEquation; expressionIso-compose; expressionIso-inverse; expressionIso-id; compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.Naturality 𝒯 M ℱ P I E S using (naturality)

abstract
  cancel-source-component : {Γ C D : CAT} {F G : MAP C D}
    (α : MorphismExpression F G) {x y : MAP Γ C} (f g : MorphismExpression x y) →
    IsInvertibleExpression (restrict-expression α x) →
    ExpressionIso (post-expression F f) (post-expression F g) →
    ExpressionIso (post-expression G f) (post-expression G g)
  cancel-source-component α {x} {y} f g w same =
    InverseEquation.reflect-before W.right-inverse (restrict-expression α x) W.right-inverse-law
      (post-expression _ f) (post-expression _ g)
      (expressionIso-compose (expressionIso-inverse (naturality α g))
        (expressionIso-compose (compose-expression-cong same (expressionIso-id (restrict-expression α y)))
          (naturality α f)))
    where module W = IsInvertibleExpression w

  cancel-target-component : {Γ C D : CAT} {F G : MAP C D}
    (α : MorphismExpression F G) {x y : MAP Γ C} (f g : MorphismExpression x y) →
    IsInvertibleExpression (restrict-expression α y) →
    ExpressionIso (post-expression G f) (post-expression G g) →
    ExpressionIso (post-expression F f) (post-expression F g)
  cancel-target-component α {x} {y} f g w same =
    InverseEquation.reflect-after (restrict-expression α y) W.left-inverse W.left-inverse-law
      (post-expression _ f) (post-expression _ g)
      (expressionIso-compose (naturality α g)
        (expressionIso-compose (compose-expression-cong (expressionIso-id (restrict-expression α x)) same)
          (expressionIso-inverse (naturality α f))))
    where module W = IsInvertibleExpression w
```
