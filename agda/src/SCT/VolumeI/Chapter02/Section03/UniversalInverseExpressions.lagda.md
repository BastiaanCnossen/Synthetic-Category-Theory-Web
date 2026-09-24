# The universal inverse data

The two pullback matchings of `Iso C` supply two inverse triangles for
its universal arrow. The common-edge matching is used for the second
triangle; both projections of the long-edge matching remain explicit.
The inverse equations preserve the specified endpoints and use no Rezk
assumption.

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

module SCT.VolumeI.Chapter02.Section03.UniversalInverseExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section03.InverseTriangleExpressions 𝒯 M ℱ P I E S
  using (module Right; module Left)
open import SCT.VolumeI.Chapter02.Section02.CompositionExpressions 𝒯 M ℱ P I E S using (compose-expression)
import SCT.VolumeI.Chapter02.Section03.InverseTriangleData 𝒯 M ℱ P I E as Data
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯

record IsInvertibleExpression {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) : Set m where
  field
    right-inverse : MorphismExpression y x
    left-inverse : MorphismExpression y x
    right-inverse-law : ExpressionIso (compose-expression right-inverse f) (identity-expression y)
    left-inverse-law : ExpressionIso (compose-expression f left-inverse) (identity-expression x)

module Universal (C : CAT) where
  open Data.UniversalData C public

  private
    module RightInverse = Right arrow right-triangle right-short right-long
    module LeftInverse = Left arrow left-triangle left-short left-long

  inverse-data : IsInvertibleExpression arrow
  inverse-data = record
    { right-inverse = RightInverse.inverse-expression
    ; left-inverse = LeftInverse.inverse-expression
    ; right-inverse-law = RightInverse.inverse-law
    ; left-inverse-law = LeftInverse.inverse-law }
```
