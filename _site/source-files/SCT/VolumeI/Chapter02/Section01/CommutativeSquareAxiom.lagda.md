# The commutative square axiom

`axiom:Commutative_Square_Axiom` asserts that this particular square of
shapes is a pushout. Its functor-category formulation follows from the
criterion proved in Section 1.8. No other pushouts are postulated.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.SquareShape 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P

record CommutativeSquareAxiom : Set (c ⊔ m) where
  field
    square-isPushout : IsPushout gluing-square
```
