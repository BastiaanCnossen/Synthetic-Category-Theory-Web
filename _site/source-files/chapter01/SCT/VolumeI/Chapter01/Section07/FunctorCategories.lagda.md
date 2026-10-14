# Functor categories

A category with a supplied evaluation is a functor category when its actual
evaluation-induced functor between mapping animae is an equivalence for
every test category (`def:Functor_Category`). The three assumptions below
are exactly the chosen category, evaluation and universal property of
`post:Functor_Category`. Currying and its laws are derived afterwards.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.FunctorCategories where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluation-forward)

module _ {Γ : Context} where
  IsFunctorCategory : {F C D : CAT Γ} → MAP (F × C) D → Set (c ⊔ m)
  IsFunctorCategory e = (T : CAT Γ) → IsEquiv (evaluation-forward e T)

  postulate
    Fun : CAT Γ → CAT Γ → CAT Γ
    funEval : {C D : CAT Γ} → MAP (Fun C D × C) D
    funUniversal : (C D : CAT Γ) → IsFunctorCategory (funEval {C = C} {D = D})
```
