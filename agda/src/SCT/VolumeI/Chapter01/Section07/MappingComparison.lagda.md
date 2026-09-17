# Mapping animae inside functor categories

For `prop:Mapping_Anima_Comparison`, the inclusion is the currying of
mapping-anima evaluation. Its action on mapping animae fits into the two
uncurrying equivalences. The comparison is proved on the whole mapping
anima by uncurrying, not only on absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.MappingComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section06.Evaluation 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Uncurrying 𝒯 M using (module ExponentialLaw)

mappingInclusion : (C D : CAT) → MAP (Map C D) (Fun C D)
mappingInclusion C D = funCurry mapEval

module InclusionComparison (X C D : CAT) (xAn : isAn X) where
  module U = Evaluation.At (funEval {C} {D}) X
  module V = ExponentialLaw X C D xAn
  inclusion = mappingInclusion C D

  uncurrying-square : =₁ (U.forward ∘ mapPost inclusion) V.forward
  uncurrying-square = mapReflect (map-isAn X (Map C D)) _ _
    (invIso V.forward-β ∙
      (((funCurry-β mapEval ▷ productMap mapEval (id C)) ∙
        (funUncurry-pre inclusion mapEval ∙ funUncurry-cong (mapPost-β inclusion)))
          ▷ Associativity.backward (Map X (Map C D)) X C) ∙
      U.represents (mapPost inclusion))

  inclusion-isEquiv : IsEquiv (mapPost {C = X} inclusion)
  inclusion-isEquiv = equiv-cancel-left (mapPost inclusion) U.forward
    (funUniversal C D X) (equiv-transport (invIso uncurrying-square) V.forward-isEquiv)
```

