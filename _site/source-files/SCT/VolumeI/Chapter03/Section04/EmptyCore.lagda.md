# A category with empty core is empty

Suppose its core admits a map to the strict initial category. Endpoint
restriction then also maps its anima of arrows to the initial category.
Strictness makes the constant-arrow map an equivalence. The
morphismwise groupoid criterion and recognition identify the category
with its core, giving the required map to the initial category.

The criterion is an explicit input to this supporting lemma. The final
Chapter 3 theorem supplies its proof; it is not an additional axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition
import SCT.VolumeI.Chapter01.Section05.Initial as Initial

module SCT.VolumeI.Chapter03.Section04.EmptyCore
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R)
  (Z : Initial.InitialStructure 𝒯 M) (strict : Initial.StrictInitial 𝒯 M Z) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open Initial.Initiality 𝒯 M Z
open Initial.StrictInitial strict
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; core-of-anima)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open Recognition.RecognitionAxiom N using (groupoid-isAn)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (constantMap)

module Detection (detect : (C : CAT) → IsEquiv (constantMap C) → IsGroupoid C)
  (C : CAT) (empty-core : MAP (Core C) Zero) where

  empty-arrows : MAP (Map [1] C) Zero
  empty-arrows = empty-core ∘ mapPre zero

  constants-equivalent : IsEquiv (constantMap C)
  constants-equivalent = equiv-cancel-left (constantMap C) empty-arrows
    (into-zero-isEquiv empty-arrows) (into-zero-isEquiv (empty-arrows ∘ constantMap C))

  category-isAn : isAn C
  category-isAn = groupoid-isAn (detect C constants-equivalent)

  to-empty : MAP C Zero
  to-empty = empty-core ∘ IsEquiv.inverse (core-of-anima C category-isAn)

  initial-isEquiv : IsEquiv (initiate C)
  initial-isEquiv = equiv-cancel-left (initiate C) to-empty
    (into-zero-isEquiv to-empty) (into-zero-isEquiv (to-empty ∘ initiate C))
```
