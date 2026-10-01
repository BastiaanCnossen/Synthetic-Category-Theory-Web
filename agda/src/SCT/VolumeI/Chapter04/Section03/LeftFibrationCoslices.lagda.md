# Left fibrations induce equivalences on coslices

Base change of the source-evaluation pullback square at a chosen object
shows that the induced coslice functor is an equivalence. This direction
needs no pointwise detection or functoriality of universals. The theorem
concerns `CosliceFunctors.Image`, with its specified cone computation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.LeftFibrationCoslices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.CosliceFunctors 𝒯 M ℱ P I public hiding (module At)
open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I
  using (module Criterion; module Evaluation)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacksLeft as Transport

module At {C D : CAT} (F : MAP C D) (e : IsEquiv (Evaluation.directed-ev₀ F))
  (x : Obj-abs C) where
  private
    module Functor = Image F x using (cospan; functor; computation; projection)
    module Source = CosliceEndpoint x using (square; square-isPullback)
    module Target = CosliceEndpoint (F ∘ x) using (square; square-isPullback)
    module Preserved = Transport.Mapped 𝒯 P Functor.cospan
      (Criterion.left-to-pullback F e) Source.square Source.square-isPullback
      using (module Specified)
    module Result = Preserved.Specified Target.square Target.square-isPullback
      Functor.functor Functor.computation using (comparison-isEquiv)

  abstract
    isEquiv : IsEquiv Functor.functor
    isEquiv = Result.comparison-isEquiv (id-isEquiv One)

  open Functor public using (functor; computation; projection)

  equivalence : Equiv (Coslice C x) (Coslice D (F ∘ x))
  equivalence = record { functor = functor ; isEquiv = isEquiv }
```
