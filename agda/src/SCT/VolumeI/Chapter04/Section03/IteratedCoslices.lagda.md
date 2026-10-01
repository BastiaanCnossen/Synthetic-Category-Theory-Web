# Flattening an iterated coslice

The projection from `C_{x/}` is a left fibration. Its induced coslice
functor therefore identifies `(C_{x/})_{u/}` with `C_{y/}`, where `y` is
the target of `u`. This module records the actual induced functor, its
whole source-endpoint computation, and the comparison over `C`.
The further comparison over `C_{x/}` with precomposition is separate.

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

module SCT.VolumeI.Chapter04.Section03.IteratedCoslices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section03.SliceFibrations 𝒯 M ℱ P I E S Q public
import SCT.VolumeI.Chapter04.Section03.LeftFibrationCoslices as Coslices
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)

module At {C : CAT} (x : Obj-abs C) (u : Obj-abs (Coslice C x)) where
  target-object : Obj-abs C
  target-object = coslice-projection x ∘ u

  private
    module Result = Coslices.At 𝒯 M ℱ P I (coslice-projection x)
      (coslice-isLeftFibration x) u using (functor; isEquiv; computation; projection; equivalence)
  open Result public using (functor; isEquiv; computation; projection; equivalence)

  over-targets : FunctorOver (coslice-projection x ∘ coslice-projection u)
    (coslice-projection target-object)
  over-targets = record { lift = functor ; comparison = projection }
```

