# Interchange for natural transformations

Precomposition and postcomposition give the four sides of the interchange
square. We compare them with the action of the internal composition functor
on a pair of transformations. Composition in products and the unit laws
identify both routes, with the same named-composite comparison at each vertex.
Gluing the two composite triangles then supplies the commutative square.

This proves the manuscript's statement with explicit endpoint choices. The
square is constructed by gluing, rather than by its displayed double currying.
We do not assert that these two specified square witnesses are identified.

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

module SCT.VolumeI.Chapter02.Section02.Interchange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationComparisons 𝒯 M ℱ P I E S using (change-long)
import SCT.VolumeI.Chapter02.Section02.InternalComposition as Internal
import SCT.VolumeI.Chapter02.Section02.ProductInterchange as Product
import SCT.VolumeI.Chapter02.Section02.NaturalTransformationWhiskering as NaturalActions
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.GluedFramedSquares as Gluing
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.ArrowCategorySquares 𝒯 M ℱ P I E S using (FramedSquare)

module At {B C D : CAT} {F G : MAP C D} {u v : MAP B C}
  (α : MorphismExpression (nameFun F) (nameFun G))
  (β : MorphismExpression (nameFun u) (nameFun v)) where
  module InternalAction = Internal.At 𝒯 M ℱ B C D
  module Base = Product.At 𝒯 M ℱ P I E S {Γ = One} {A = Fun C D} {B = Fun B C} {C = Fun B D}
    InternalAction.composeFunctor {x = nameFun F} {x′ = nameFun G} {y = nameFun u} {y′ = nameFun v} α β
  module Top = NaturalActions.Pre 𝒯 M ℱ P I E S {B} {C} {D} u {F} {G} α
  module Right = NaturalActions.Post 𝒯 M ℱ P I E S {B} {C} {D} G {u} {v} β
  module Left = NaturalActions.Post 𝒯 M ℱ P I E S {B} {C} {D} F {u} {v} β
  module Bottom = NaturalActions.Pre 𝒯 M ℱ P I E S {B} {C} {D} v {F} {G} α
  κ₀₀ = InternalAction.Named.comparison F u
  κ₀₁ = InternalAction.Named.comparison G u
  κ₁₀ = InternalAction.Named.comparison F v
  κ₁₁ = InternalAction.Named.comparison G v

  paired-first : MorphismExpression (nameFun (F ∘ u)) (nameFun (G ∘ v))
  paired-first = compose-expression (retarget-expression Base.top κ₀₀ κ₀₁)
    (retarget-expression Base.right κ₀₁ κ₁₁)
  transported-first : MorphismExpression (nameFun (F ∘ u)) (nameFun (G ∘ v))
  transported-first = retarget-expression (compose-expression Base.top Base.right) κ₀₀ κ₁₁
  transported-second : MorphismExpression (nameFun (F ∘ u)) (nameFun (G ∘ v))
  transported-second = retarget-expression (compose-expression Base.left Base.bottom) κ₀₀ κ₁₁
  paired-second : MorphismExpression (nameFun (F ∘ u)) (nameFun (G ∘ v))
  paired-second = compose-expression (retarget-expression Base.left κ₀₀ κ₁₀)
    (retarget-expression Base.bottom κ₁₀ κ₁₁)

  abstract
    first-edges : ExpressionIso (compose-expression Top.action Right.action) paired-first
    first-edges = expressionIso-inverse (compose-expression-cong Top.comparison Right.comparison)
    first-composite : ExpressionIso paired-first transported-first
    first-composite = retarget-composition Base.top Base.right κ₀₀ κ₀₁ κ₁₁
    product-comparison : ExpressionIso transported-first transported-second
    product-comparison = retarget-expressionIso Base.comparison κ₀₀ κ₁₁
    second-composite : ExpressionIso transported-second paired-second
    second-composite = expressionIso-inverse (retarget-composition Base.left Base.bottom κ₀₀ κ₁₀ κ₁₁)
    second-edges : ExpressionIso paired-second (compose-expression Left.action Bottom.action)
    second-edges = compose-expression-cong Left.comparison Bottom.comparison

    comparison : ExpressionIso (compose-expression Top.action Right.action)
      (compose-expression Left.action Bottom.action)
    comparison = expressionIso-compose second-edges
      (expressionIso-compose second-composite
        (expressionIso-compose product-comparison
          (expressionIso-compose first-composite first-edges)))

  module Square (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where
    square : FramedSquare Top.action Right.action Left.action Bottom.action
    square = Gluing.At.square 𝒯 M ℱ P I E S Q
      (composition-presentation Top.action Right.action)
      (change-long (composition-presentation Left.action Bottom.action)
        (expressionIso-inverse comparison))

open NaturalActions 𝒯 M ℱ P I E S using (pre-whisker; post-whisker)

interchange : {B C D : CAT} {F G : MAP C D} {u v : MAP B C}
  (α : MorphismExpression (nameFun F) (nameFun G))
  (β : MorphismExpression (nameFun u) (nameFun v)) →
  ExpressionIso (compose-expression (pre-whisker u α) (post-whisker G β))
    (compose-expression (post-whisker F β) (pre-whisker v α))
interchange {B} {C} {D} {F} {G} {u} {v} α β = At.comparison {B} {C} {D} {F} {G} {u} {v} α β
```
