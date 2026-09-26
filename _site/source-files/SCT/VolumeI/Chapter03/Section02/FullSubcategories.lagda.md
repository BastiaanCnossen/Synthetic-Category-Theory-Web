# Full subcategories

Restriction to cores is the mapping action with test category `One`
(`con:Restriction_To_Groupoid_Cores`). This gives the defining square
of `def:Full_Subcategory`, with its specified commutativity identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section02.FullSubcategories
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
  using (mapPost; mapPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; base-change-embedding; equivalence-isEmbedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P
  using (map-preserves-embedding; map-detects-embedding)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
  using (degenerate-pullback; degenerate-pullback-converse)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M
  using (mappingAction; mappingAction-natural)

restrictionToCores : (C D : CAT) → MAP (Map C D) (Map (Core C) (Core D))
restrictionToCores = mappingAction One

fullSubcategorySquare : {A C : CAT} (f : MAP A C) (D : CAT) →
  Cone (restrictionToCores D C) (mapPost (mapPost {C = One} f)) (Map D A)
fullSubcategorySquare {A} f D = record
  { left = mapPost f
  ; right = restrictionToCores D A
  ; match = (mappingAction-natural One D f) ⁻¹ }

record IsFullSubcategory {A C : CAT} (f : MAP A C) : Set (c ⊔ m) where
  field
    core-isEmbedding : IsEmbedding (mapPost {C = One} f)
    mapping-square-isPullback : (D : CAT) → IsPullback (fullSubcategorySquare f D)

full-subcategory-isEmbedding : {A C : CAT} (f : MAP A C) →
  IsFullSubcategory f → IsEmbedding f
full-subcategory-isEmbedding f sub = map-detects-embedding f (λ D →
  base-change-embedding (fullSubcategorySquare f D)
    (IsFullSubcategory.mapping-square-isPullback sub D)
    (map-preserves-embedding (Core D) (mapPost f)
      (IsFullSubcategory.core-isEmbedding sub)))
```

The last lemma in the section can already be proved from this definition.
A full subcategory is an equivalence precisely when its map on cores is
an equivalence (`lem:Full_Subcategory_Is_Equivalence_Iff_Equivalence_On_Objects`).
Again the proof tests mapping animae and uses the defining pullback square.

```agda
full-subcategory-core-detects-equivalence : {A C : CAT} (f : MAP A C) →
  IsFullSubcategory f → IsEquiv (mapPost {C = One} f) → IsEquiv f
full-subcategory-core-detects-equivalence f sub core-equiv = post-tests-all f (λ D →
  degenerate-pullback-converse (mapPost-isEquiv (mapPost f) core-equiv)
    (fullSubcategorySquare f D) (IsFullSubcategory.mapping-square-isPullback sub D))

equivalence-on-cores : {A C : CAT} (f : MAP A C) →
  IsEquiv f → IsEquiv (mapPost {C = One} f)
equivalence-on-cores = mapPost-isEquiv

equivalence-isFullSubcategory : {A C : CAT} (f : MAP A C) →
  IsEquiv f → IsFullSubcategory f
equivalence-isFullSubcategory f ef = record
  { core-isEmbedding = equivalence-isEmbedding (mapPost f) (mapPost-isEquiv f ef)
  ; mapping-square-isPullback = λ D → degenerate-pullback
      (mapPost-isEquiv (mapPost f) (mapPost-isEquiv f ef))
      (fullSubcategorySquare f D) (mapPost-isEquiv f ef) }
```
