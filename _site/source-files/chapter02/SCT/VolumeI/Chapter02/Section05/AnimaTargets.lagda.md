# Functor categories with an anima target

For any category A and anima X, Fun(A,X) is an anima: the structural groupoid
property is preserved by functor categories, and recognition converts it back
to the primitive anima predicate.

The canonical inclusion Map(A,X) → Fun(A,X) is therefore an equivalence
(`Map_is_Fun_for_groupoids`). We use the established comparison with the core
and its actual inclusion triangle. This proves the claim for the specified
mapping inclusion, not merely for an unspecified equivalence of categories.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section05.AnimaTargets where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-transport)
open import SCT.VolumeI.Chapter01.Section04.Core
  using (coreInclusion; core-of-anima)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun
  using (mappingInclusion; coreFunComparison; coreFunComparison-isEquiv;
    coreFunComparison-inclusion)
open import SCT.VolumeI.Chapter02.Section04.FunctorGroupoids
  using (functor-isGroupoid)
open import SCT.VolumeI.Chapter02.Section05.Recognition
  using (anima-isGroupoid; groupoid-isAn)

module _ {Γ : Context} where
  functor-isAn : (A X : CAT Γ) → isAn X → isAn (Fun A X)
  functor-isAn A X h = groupoid-isAn (functor-isGroupoid A (anima-isGroupoid h))

  mappingInclusion-isEquiv : (A X : CAT Γ) → isAn X
    → IsEquiv (mappingInclusion A X)
  mappingInclusion-isEquiv A X h =
    equiv-transport (coreFunComparison-inclusion A X)
      (equiv-compose (coreFunComparison A X) (coreInclusion (Fun A X))
        (coreFunComparison-isEquiv A X) (core-of-anima (Fun A X) (functor-isAn A X h)))
```
