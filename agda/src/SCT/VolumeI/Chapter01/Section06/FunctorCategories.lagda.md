# Functor categories and their axiom

`IsFunctorCategory` is `def:Functor_Category`: the actual functor induced by
evaluation is an equivalence for every test category. `FunctorCategories`
is precisely `post:Functor_Category`. Currying and its computation rules
will be derived, rather than included among the fields.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section06.FunctorCategories
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Evaluation 𝒯 M

IsFunctorCategory : {F C D : CAT} → MAP (F × C) D → Set (c ⊔ m)
IsFunctorCategory e = (T : CAT) → IsEquiv (Evaluation.At.forward e T)

record FunctorCategories : Set (c ⊔ m) where
  field
    Fun : CAT → CAT → CAT
    funEval : {C D : CAT} → MAP (Fun C D × C) D
    funUniversal : (C D : CAT) → IsFunctorCategory (funEval {C} {D})
```
