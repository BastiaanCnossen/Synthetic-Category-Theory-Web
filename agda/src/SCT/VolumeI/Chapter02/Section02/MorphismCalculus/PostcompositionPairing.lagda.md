# Applying a paired functor to a transformation

Postcomposition by a pair of functors is the pair of the two
postcompositions. The endpoint identifications are the chosen comparison
for precomposition of pairing.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPairing
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.FixedCoordinateExpressions as Fixed
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting

module At {Γ A B C : CAT} (F : MAP A B) (G : MAP A C)
  {x y : MAP Γ A} (α : MorphismExpression x y) where
  module First = Pasting.At 𝒯 M ℱ P I E (pair F G) pr₁ F (pair-β₁ F G) α
  module Second = Pasting.At 𝒯 M ℱ P I E (pair F G) pr₂ G (pair-β₂ F G) α
  module Compared = Fixed.Pairing 𝒯 M ℱ P I E S (pair F G) α (post-expression F α) (post-expression G α)
    First.source-change First.target-change Second.source-change Second.target-change
    First.comparison Second.comparison

  value : ExpressionIso
    (retarget-expression (post-expression (pair F G) α) (pair-pre F G x) (pair-pre F G y))
    (pair-expression (post-expression F α) (post-expression G α))
  value = Compared.comparison
```
