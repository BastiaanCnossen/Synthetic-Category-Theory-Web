# Currying and uncurrying

This is `def:Currying`, with the chosen functor category as target. The
operations and their beta, eta, and parameter-change comparisons are
specializations of the preceding representability argument.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.Currying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Categories.FunctorCategories F public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.Representation 𝒯 M

module _ {C D : CAT} where
  open Representing (funEval {C} {D}) (funUniversal C D) public
    using () renaming
      (uncurry to funUncurry; uncurry-cong to funUncurry-cong;
       uncurry-restrict to funUncurry-restrict;
       curry to funCurry; curry-β to funCurry-β; curry-η to funCurry-η;
       curry-cong to funCurry-cong; curry-restrict to funCurry-restrict; reflect to funReflect)
```

```agda
funUncurry-id : (C D : CAT) → (funUncurry (id (Fun C D))) =₁ (funEval {C} {D})
funUncurry-id C D = Representing.uncurry-id (funEval {C} {D}) (funUniversal C D)
```
