# The ordinary mapping-anima criterion for localization

This follows `prop:localization_as_ordinary_universal_property`. Compare
with the localization supplied by the axiom, prove the comparison an
equivalence by testing mapping animae, then transfer the functor-category
universal property.

The comparison triangle has vertex `Map^W(C,D)`, as in the corrected
manuscript. Reflection through its embedding into `Map(C,D)` supplies
the commutativity identification in that triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.LocalizationCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (pre-tests-all)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ
  using (funPre; funPre-comp; funPre-cong; funPre-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-reflect)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (full-subcategory-isEmbedding)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts; module Inverting)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationRestriction 𝒯 M ℱ P I E S Q R using (module RestrictionAlong)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMapping 𝒯 M ℱ P I E S Q using (module OnMaps)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.MappingLocalizationLifts 𝒯 M ℱ P I E S Q
  using () renaming (module Lift to MappingLift)

module Criterion (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L)
  {C T : CAT} (W : MorphismCollection C) (l : MAP C T) (inverts : Inverts l W)
  (restriction : (D : CAT) → FunctorLift (Inverting.inclusion W D) (mapPre l))
  (universal : (D : CAT) → IsEquiv (FunctorLift.lift (restriction D))) where
  open WithSubcategories L
  existing : Localization W
  existing = LocalizationAxiom.localized Z W
  T₀ : CAT
  T₀ = Localization.category existing
  l₀ : MAP C T₀
  l₀ = Localization.functor existing
  property : IsLocalization W l₀
  property = Localization.isLocalization existing
  inverts₀ : Inverts l₀ W
  inverts₀ = IsLocalization.inverts property

  module Existing (D : CAT) where
    module Maps = OnMaps L W l₀ D (RestrictionAlong.factorization L W l₀ inverts₀ D)
      using (maps; comparison; isEquiv)
    maps = Maps.maps
    comparison = Maps.comparison
    isEquiv = Maps.isEquiv (IsLocalization.universal property D)

  module Compare = MappingLift W l (restriction T₀) (universal T₀) l₀ inverts₀
    using (factor; comparison)
  u : MAP T T₀
  u = Compare.factor

  module Tested (D : CAT) where
    q = FunctorLift.lift (restriction D)
    inclusion = Inverting.inclusion W D
    triangle : (q ∘ mapPre u) =₁ Existing.maps D
    triangle = embedding-reflect inclusion (Inverting.inclusion-isEmbedding W D) _ _
      ((Existing.comparison D) ⁻¹ ∙
        (mapPre-cong Compare.comparison ∙
          (mapPre-comp l u ∙
            ((FunctorLift.comparison (restriction D) ▷ mapPre u) ∙
              (comp-assoc (mapPre u) q inclusion) ⁻¹))))

    restriction-isEquiv : IsEquiv (mapPre {D = D} u)
    restriction-isEquiv = equiv-cancel-left (mapPre u) q (universal D)
      (equiv-transport (triangle ⁻¹) (Existing.isEquiv D))

  comparison-isEquiv : IsEquiv u
  comparison-isEquiv = pre-tests-all u Tested.restriction-isEquiv

  module Enriched (D : CAT) where
    module Target = Inverting.Category W D L
    module Proposed = RestrictionAlong L W l inverts D
    module Known = RestrictionAlong L W l₀ inverts₀ D

    triangle : (Proposed.functor ∘ funPre u) =₁ Known.functor
    triangle = embedding-reflect Target.functorInclusion
      (full-subcategory-isEmbedding Target.functorInclusion Target.isFullSubcategory) _ _
      (Known.comparison ⁻¹ ∙
        (funPre-cong Compare.comparison ∙
          (funPre-comp l u ∙
            ((Proposed.comparison ▷ funPre u) ∙
              (comp-assoc (funPre u) Proposed.functor Target.functorInclusion) ⁻¹))))

    isEquiv : IsEquiv Proposed.functor
    isEquiv = equiv-cancel-right (funPre u) Proposed.functor (funPre-isEquiv u comparison-isEquiv)
      (equiv-transport (triangle ⁻¹) (IsLocalization.universal property D))

  isLocalization : IsLocalization W l
  isLocalization = record { inverts = inverts ; universal = Enriched.isEquiv }
```
