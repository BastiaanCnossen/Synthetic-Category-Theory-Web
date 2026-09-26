# Collections of objects and their morphisms

This is `def:Collection_Of_Objects`. A collection is an anima embedded
in the core. Its associated morphism collection consists of arrows whose
two endpoints lie in the collection. The defining pullback retains its
matching with the product of the two core inclusions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter03.Section02.ObjectCollections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; core-isAn)
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPre)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; chosen-base-change-embedding; equivalence-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section02.Factorization.ProductEmbeddings 𝒯 P using (productMap-isEmbedding)

record ObjectCollection (C : CAT) : Set (c ⊔ m ⊔ a) where
  field
    collection : CAT
    collection-isAn : isAn collection
    inclusion : MAP collection (Core C)
    inclusion-isEmbedding : IsEmbedding inclusion

allObjects : (C : CAT) → ObjectCollection C
allObjects C = record { collection = Core C ; collection-isAn = core-isAn C
  ; inclusion = id (Core C) ; inclusion-isEmbedding = equivalence-isEmbedding _ (id-isEquiv _) }

endpoints : (C : CAT) → MAP (Map [1] C) (Core C × Core C)
endpoints C = pair (mapPre zero) (mapPre one)

module SpannedMorphisms {C : CAT} (V : ObjectCollection C) where
  open ObjectCollection V

  morphisms : CAT
  morphisms = Pullback (endpoints C) (productMap inclusion inclusion)

  morphisms-isAn : isAn morphisms
  morphisms-isAn = pullback-isAn _ _ (map-isAn [1] C)
    (product-isAn collection-isAn collection-isAn) (product-isAn (core-isAn C) (core-isAn C))

  morphisms-inclusion : MAP morphisms (Map [1] C)
  morphisms-inclusion = pullback₁

  morphisms-inclusion-isEmbedding : IsEmbedding morphisms-inclusion
  morphisms-inclusion-isEmbedding = chosen-base-change-embedding (endpoints C) _
    (productMap-isEmbedding inclusion inclusion inclusion-isEmbedding inclusion-isEmbedding)

  collectionOfMorphisms : MorphismCollection C
  collectionOfMorphisms = record
    { collection = morphisms ; collection-isAn = morphisms-isAn
    ; inclusion = morphisms-inclusion ; inclusion-isEmbedding = morphisms-inclusion-isEmbedding }
```
