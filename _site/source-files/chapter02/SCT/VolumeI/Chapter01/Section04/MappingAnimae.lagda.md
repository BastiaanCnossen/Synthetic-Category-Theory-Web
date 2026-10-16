# Evaluation and currying for mapping animae

`Map C D` is the internal mapping anima. Uncurrying has an arbitrary
source `A`; currying and the equivalence of its specified action require
`isAn A`. These are the six existing mapping-anima assumptions.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.MappingAnimae where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong)

module _ {Γ : Context} where
  postulate
    Map : CAT Γ → CAT Γ → CAT Γ
    map-isAn : (C D : CAT Γ) → isAn (Map C D)
    mapEval : {C D : CAT Γ} → MAP (Map C D × C) D

  module _ {A : CAT Γ} where
    open Terms.InContext A using (Term)

    uncurry : {C D : CAT Γ} → Term (Map C D) → MAP (A × C) D
    uncurry {C = C} f = mapEval ∘ productMap f (id C)

    postulate
      mapCurry : {C D : CAT Γ} → isAn A → MAP (A × C) D → Term (Map C D)
      mapCurry-β : {C D : CAT Γ} (aAn : isAn A) (h : MAP (A × C) D)
        → uncurry (mapCurry aAn h) =₁ h

    uncurry⁼-functor : {C D : CAT Γ} (f g : Term (Map C D))
      → MAP (Equal f g) (Equal (uncurry f) (uncurry g))
    uncurry⁼-functor {C = C} f g = postWhisker mapEval ∘
      productMap-cong (id (Equal f g)) (const (id₌ (id C)))

    postulate
      uncurry⁼-isEquiv : {C D : CAT Γ} (aAn : isAn A)
        (f g : Term (Map C D)) → IsEquiv (uncurry⁼-functor f g)
```

`productMap-cong` is the former `productFamily`: both use the same
chosen inverse of product coordinates on the same transported projections.
The equivalence axiom therefore concerns the original specified action.
No strict beta equation or change-of-ambient-context law is added.
