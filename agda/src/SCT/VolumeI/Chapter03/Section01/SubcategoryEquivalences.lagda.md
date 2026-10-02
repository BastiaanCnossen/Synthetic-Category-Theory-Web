# Changing the presentation of a subcategory

An equivalence of sources over the ambient category preserves the
subcategory property. To prove this for the specified square, transport
the proposed family of morphisms across the equivalence, use the given
subcategory property, and lift back. The embedding pullback criterion
then supplies the universal property, including the specified matching.
The argument is shared with full subcategories: it is `ChangeSource` of
`TestedInclusions` at `K = [1]`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter03.Section01.SubcategoryEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.TestedInclusions 𝒯 M P
  using () renaming (module ChangeSource to TestedChangeSource)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I

module ChangeSource {A B C : CAT} (f : MAP A C) (g : MAP B C)
  (e : MAP A B) (equivalent : IsEquiv e) (over : (g ∘ e) =₁ f)
  (full : IsSubcategory g) where

  module Change = TestedChangeSource [1] f g e equivalent over
    (IsSubcategory.morphisms-isEmbedding full) (IsSubcategory.mapping-square-isPullback full)
  open Change public using (embedding; module Square)

  isSubcategory : IsSubcategory f
  isSubcategory = record
    { morphisms-isEmbedding = Change.test-isEmbedding
    ; mapping-square-isPullback = Change.square-isPullback }

subcategory-precompose-equivalence : {A B C : CAT}
  (f : MAP A C) (g : MAP B C) (e : MAP A B) → IsEquiv e →
  (g ∘ e) =₁ f → IsSubcategory g → IsSubcategory f
subcategory-precompose-equivalence = ChangeSource.isSubcategory
```
