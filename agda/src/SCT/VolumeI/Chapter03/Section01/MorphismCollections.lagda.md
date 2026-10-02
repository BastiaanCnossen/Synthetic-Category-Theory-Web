# Collections of morphisms

A collection is an anima embedded in `Map [1] C`
(`def:Collection_Of_Morphisms`). Membership means factorization of the
point representing an arrow, as in `conv:Morphisms_In_A_Collection`.
It does not mean being a morphism internal to the collection's anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter03.Section01.MorphismCollections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (nameMap)
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
  using (mapPost; mapPost-id; mapPost-comp; mapPre)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-reflect; equivalence-isEmbedding)
open import SCT.VolumeI.Chapter01.Section03.FactorizationCalculus
  vocabulary terminal products productLaws composition
  using (lift-id; lift-retarget; lift-compose-along; lift-unique)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I using (IsSubcategory)

record MorphismCollection (C : CAT) : Set (c ⊔ m ⊔ a) where
  field
    collection : CAT
    collection-isAn : isAn collection
    inclusion : MAP collection (Map [1] C)
    inclusion-isEmbedding : IsEmbedding inclusion

  Contains : MAP [1] C → Set m
  Contains f = FunctorLift inclusion (nameMap f)

  membership-unique : (f : MAP [1] C) (u v : Contains f) →
    FunctorLift.lift u =₁ FunctorLift.lift v
  membership-unique f = lift-unique (embedding-reflect inclusion inclusion-isEmbedding)

abstract
  all-morphisms-inclusion-isEmbedding : (C : CAT) → IsEmbedding (id (Map [1] C))
  all-morphisms-inclusion-isEmbedding C = equivalence-isEmbedding _ (id-isEquiv _)

allMorphisms : (C : CAT) → MorphismCollection C
allMorphisms C = record
  { collection = Map [1] C
  ; collection-isAn = map-isAn [1] C
  ; inclusion = id (Map [1] C)
  ; inclusion-isEmbedding = all-morphisms-inclusion-isEmbedding C }

subcategoryMorphisms : {A C : CAT} (f : MAP A C) → IsSubcategory f → MorphismCollection C
subcategoryMorphisms {A} f sub = record
  { collection = Map [1] A
  ; collection-isAn = map-isAn [1] A
  ; inclusion = mapPost f
  ; inclusion-isEmbedding = IsSubcategory.morphisms-isEmbedding sub }

record ClosedUnderIdentities {C : CAT} (W : MorphismCollection C) : Set m where
  open MorphismCollection W
  field
    source-identity : FunctorLift inclusion (mapPre (const zero) ∘ inclusion)
    target-identity : FunctorLift inclusion (mapPre (const one) ∘ inclusion)
```

A functor preserves collections when its action on arrows factors through
the specified target collection (`def:Functor_Preserving_Morphisms`).
The factorization retains its comparison with the inclusions. Identities
and composites are the corresponding operations on factorizations,
retargeted along functoriality of `mapPost`.

```agda
PreservesMorphisms : {C D : CAT} → MAP C D → MorphismCollection C → MorphismCollection D → Set m
PreservesMorphisms f V W = FunctorLift (MorphismCollection.inclusion W)
  (mapPost f ∘ MorphismCollection.inclusion V)

identity-preserves : {C : CAT} (W : MorphismCollection C) → PreservesMorphisms (id C) W W
identity-preserves {C} W = lift-retarget
  ((comp-unitˡ inclusion ∙ (mapPost-id [1] C ▷ inclusion)) ⁻¹) (lift-id inclusion)
  where open MorphismCollection W

composition-preserves : {C D E : CAT} (f : MAP C D) (g : MAP D E)
  {U : MorphismCollection C} {V : MorphismCollection D} {W : MorphismCollection E} →
  PreservesMorphisms f U V → PreservesMorphisms g V W → PreservesMorphisms (g ∘ f) U W
composition-preserves f g {U} F G = lift-retarget (mapPost-comp f g ▷ MorphismCollection.inclusion U)
  (lift-retarget ((comp-assoc (MorphismCollection.inclusion U) (mapPost f) (mapPost g)) ⁻¹)
    (lift-compose-along (mapPost g) G F))
```
