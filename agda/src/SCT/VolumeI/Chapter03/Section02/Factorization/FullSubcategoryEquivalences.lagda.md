# Changing the presentation of a full subcategory

An equivalence of sources over the ambient category preserves the full
subcategory property. To prove this for the specified square, transport
the proposed family of objects across the equivalence, use fullness of
the given presentation, and lift back. The embedding pullback criterion
then supplies the universal property, including the specified matching.
The argument is shared with subcategories: it is `ChangeSource` of
`TestedInclusions` at `K = One`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.TestedInclusions 𝒯 M P
  using () renaming (module ChangeSource to TestedChangeSource)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P

module ChangeSource {A B C : CAT} (f : MAP A C) (g : MAP B C)
  (e : MAP A B) (equivalent : IsEquiv e) (over : (g ∘ e) =₁ f)
  (full : IsFullSubcategory g) where

  module Change = TestedChangeSource One f g e equivalent over
    (IsFullSubcategory.core-isEmbedding full) (IsFullSubcategory.mapping-square-isPullback full)
  open Change public using (embedding; module Square)

  isFullSubcategory : IsFullSubcategory f
  isFullSubcategory = record
    { core-isEmbedding = Change.test-isEmbedding
    ; mapping-square-isPullback = Change.square-isPullback }

full-subcategory-precompose-equivalence : {A B C : CAT}
  (f : MAP A C) (g : MAP B C) (e : MAP A B) → IsEquiv e →
  (g ∘ e) =₁ f → IsFullSubcategory g → IsFullSubcategory f
full-subcategory-precompose-equivalence = ChangeSource.isFullSubcategory
```
