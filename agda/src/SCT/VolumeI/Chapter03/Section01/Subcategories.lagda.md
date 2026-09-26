# Subcategories

The definition is `def:Subcategory`: the induced map on morphisms is an
embedding, and a functor factors through the subcategory precisely when
its action on morphisms does. The square includes the commutativity
identification constructed in `MappingAction`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter03.Section01.Subcategories
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPost; mapPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; base-change-embedding; equivalence-isEmbedding)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
  using (degenerate-pullback)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P
  using (map-preserves-embedding; map-detects-embedding)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M
  using (mappingAction; mappingAction-natural)

subcategorySquare : {A C : CAT} (f : MAP A C) (D : CAT) →
  Cone (mappingAction [1] D C) (mapPost (mapPost {C = [1]} f)) (Map D A)
subcategorySquare {A} f D = record
  { left = mapPost f
  ; right = mappingAction [1] D A
  ; match = (mappingAction-natural [1] D f) ⁻¹ }

record IsSubcategory {A C : CAT} (f : MAP A C) : Set (c ⊔ m) where
  field
    morphisms-isEmbedding : IsEmbedding (mapPost {C = [1]} f)
    mapping-square-isPullback : (D : CAT) → IsPullback (subcategorySquare f D)
```

Every subcategory is an embedding (`lem:Subcategory_Is_Embedding`). Test on
mapping animae. Each tested map is a base change of the map induced by the
embedding on morphisms, exactly as in the manuscript's proof.

```agda
subcategory-isEmbedding : {A C : CAT} (f : MAP A C) →
  IsSubcategory f → IsEmbedding f
subcategory-isEmbedding f sub = map-detects-embedding f (λ D →
  base-change-embedding (subcategorySquare f D)
    (IsSubcategory.mapping-square-isPullback sub D)
    (map-preserves-embedding (Map [1] D) (mapPost f)
      (IsSubcategory.morphisms-isEmbedding sub)))

equivalence-isSubcategory : {A C : CAT} (f : MAP A C) →
  IsEquiv f → IsSubcategory f
equivalence-isSubcategory f ef = record
  { morphisms-isEmbedding = equivalence-isEmbedding (mapPost f) (mapPost-isEquiv f ef)
  ; mapping-square-isPullback = λ D → degenerate-pullback
      (mapPost-isEquiv (mapPost f) (mapPost-isEquiv f ef))
      (subcategorySquare f D) (mapPost-isEquiv f ef) }

identity-isSubcategory : (C : CAT) → IsSubcategory (id C)
identity-isSubcategory C = equivalence-isSubcategory (id C) (id-isEquiv C)
```
