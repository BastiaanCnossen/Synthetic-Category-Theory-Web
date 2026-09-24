# Functor categories and their axiom

`IsFunctorCategory` expresses `def:Functor_Category`: the actual functor
induced by evaluation is an equivalence for every test category.
`FunctorCategories` supplies `Fun C D`, its evaluation, and this universal
property, as in `post:Functor_Category`.

Unlike currying into the mapping anima `Map C D`, currying into `Fun C D`
allows an arbitrary category as parameter. Currying and its computation
rules are derived in `Currying`, rather than included among the fields here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section07.FunctorCategories
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Evaluation 𝒯 M

IsFunctorCategory : {F C D : CAT} → MAP (F × C) D → Set (c ⊔ m)
IsFunctorCategory e = (T : CAT) → IsEquiv (Evaluation.At.forward e T)

record FunctorCategories : Set (c ⊔ m) where
  field
    Fun : CAT → CAT → CAT
    funEval : {C D : CAT} → MAP (Fun C D × C) D
    funUniversal : (C D : CAT) → IsFunctorCategory (funEval {C} {D})
```
