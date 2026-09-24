# Recognizing animae

`axiom:D_Groupoid_Core` identifies the primitive anima predicate with the
groupoid condition. The two directions below are precisely that axiom.
Closure of animae under equivalences and initiality are consequences,
not fields of the constructor interfaces.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter02.Section05.Recognition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section04.BasicClosure 𝒯 M ℱ P I E R public
open import SCT.VolumeI.Chapter01.Section05.Initial 𝒯 M using (InitialStructure; StrictInitial)

record RecognitionAxiom : Set (c ⊔ m ⊔ a) where
  field
    anima-isGroupoid : {C : CAT} → isAn C → IsGroupoid C
    groupoid-isAn : {C : CAT} → IsGroupoid C → isAn C

module Consequences (A : RecognitionAxiom) where
  open RecognitionAxiom A public

  equivalence-preserves-anima : {C D : CAT} (f : MAP C D) →
    IsEquiv f → isAn C → isAn D
  equivalence-preserves-anima f ef h = groupoid-isAn
    (equivalence-preserves-groupoid f ef (anima-isGroupoid h))

  equivalence-reflects-anima : {C D : CAT} (f : MAP C D) →
    IsEquiv f → isAn D → isAn C
  equivalence-reflects-anima f ef h = groupoid-isAn
    (equivalence-reflects-groupoid f ef (anima-isGroupoid h))

  zero-isAn : (Z : InitialStructure) → StrictInitial Z → isAn (InitialStructure.Zero Z)
  zero-isAn Z strict = groupoid-isAn (empty-isGroupoid Z strict)
```
