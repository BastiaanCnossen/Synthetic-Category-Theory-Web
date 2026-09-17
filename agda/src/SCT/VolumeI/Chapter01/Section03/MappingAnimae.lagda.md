# Evaluation and currying for mapping animae

The first record supplies the category, anima witness, evaluation, and
currying with its beta comparison. Uncurrying and its action on isomorphism
animae are constructions. The second record asserts the equivalence of that
specific action, completing the axiom in the book.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FamilyProduct

module SCT.VolumeI.Chapter01.Section03.MappingAnimae
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily)

record MappingData : Set (c ⊔ m ⊔ a) where
  field
    Map : CAT → CAT → CAT
    map-isAn : (C D : CAT) → isAn (Map C D)
    mapEval : {C D : CAT} → MAP (Map C D × C) D

  mapUncurry : {X C D : CAT} → MAP X (Map C D) → MAP (X × C) D
  mapUncurry {C = C} f = mapEval ∘ productMap f (id C)

  field
    mapCurry : {X C D : CAT} → isAn X → MAP (X × C) D → MAP X (Map C D)
    mapCurry-β : {X C D : CAT} (xAn : isAn X) (h : MAP (X × C) D)
      → NatIso (mapUncurry (mapCurry xAn h)) h

  mapUncurry-isoMap : {X C D : CAT} (f g : MAP X (Map C D))
    → MAP (f ≅ g) (mapUncurry f ≅ mapUncurry g)
  mapUncurry-isoMap {C = C} f g = postWhisker mapEval ∘
    productFamily (id (f ≅ g)) (const (idIso (id C)))

record MappingLaws (M : MappingData) : Set (c ⊔ m ⊔ a) where
  open MappingData M
  field
    mapUncurry-isoMap-isEquiv : {X C D : CAT} (xAn : isAn X)
      (f g : MAP X (Map C D)) → IsEquiv (mapUncurry-isoMap f g)

record MappingAnimae : Set (c ⊔ m ⊔ a) where
  field
    dataMap : MappingData
    lawsMap : MappingLaws dataMap
  open MappingData dataMap public
  open MappingLaws lawsMap public
```
