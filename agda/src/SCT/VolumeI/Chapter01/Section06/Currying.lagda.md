# Currying and uncurrying

This is `def:Currying`, with the chosen functor category as target. The
operations and their beta, eta, and parameter-change comparisons are
specializations of the preceding representability argument.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.Currying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open Categories.FunctorCategories F public
open import SCT.VolumeI.Chapter01.Section06.Representation 𝒯 M

module _ {C D : CAT} where
  open Representing (funEval {C} {D}) (funUniversal C D) public
    using () renaming
      (uncurry to funUncurry; uncurry-cong to funUncurry-cong;
       uncurry-pre to funUncurry-pre;
       curry to funCurry; curry-β to funCurry-β; curry-η to funCurry-η;
       curry-cong to funCurry-cong; curry-pre to funCurry-pre; reflect to funReflect)
```

```agda
funUncurry-id : (C D : CAT) → =₁ (funUncurry (id (Fun C D))) (funEval {C} {D})
funUncurry-id C D = Representing.uncurry-id (funEval {C} {D}) (funUniversal C D)
```
