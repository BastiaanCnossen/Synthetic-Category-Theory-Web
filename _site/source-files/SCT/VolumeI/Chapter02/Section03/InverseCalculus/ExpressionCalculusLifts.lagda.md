# Recognizing inverses through the opaque expression calculus

Inverse equations in the derived expression calculus give an actual lift
to the category of isomorphisms. The comparison fields transport both
equations to Segal composition before applying inverse recognition.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionCalculusLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionCalculus 𝒯 M ℱ P I E S Q public
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E using (IsoLift)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (module LiftInverse)

module At (Γ : CAT) where
  module K = ExpressionCalculus (expression-calculus Γ)
    using (composite; identity; inverse-law)

  abstract
    lift : {C : CAT} {x y : MAP Γ C}
      (f : MorphismExpression x y) (g : MorphismExpression y x) →
      ExpressionIso (K.composite g f) (K.identity y) →
      ExpressionIso (K.composite f g) (K.identity x) →
      IsoLift (MorphismExpression.arrow f)
    lift f g right left = LiftInverse.lift f g g
      (K.inverse-law g f right) (K.inverse-law f g left)
```
