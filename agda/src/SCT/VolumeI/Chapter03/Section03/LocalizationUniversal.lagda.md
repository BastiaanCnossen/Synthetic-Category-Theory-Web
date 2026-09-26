# Factoring through a localization

The functor-category universal property supplies the mapping-anima
universal property. It gives both factorization of inverting functors
and reflection of identifications after restriction.

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

module SCT.VolumeI.Chapter03.Section03.LocalizationUniversal
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-reflect)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts; module Inverting)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationRestriction 𝒯 M ℱ P I E S Q R using (module RestrictionAlong)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMapping 𝒯 M ℱ P I E S Q using (module OnMaps)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.MappingLocalizationLifts 𝒯 M ℱ P I E S Q
  using () renaming (module Lift to MappingLift)

module Universal (L : SubcategoryAxiom) {C T : CAT} (W : MorphismCollection C)
  (l : MAP C T) (localization : WithSubcategories.IsLocalization L W l) where
  open WithSubcategories L
  inverts = IsLocalization.inverts localization

  module Into (D : CAT) where
    module Maps = OnMaps L W l D (RestrictionAlong.factorization L W l inverts D)
      using (maps; comparison; factorization; isEquiv)
    restriction : MAP (Map T D) (Inverting.maps W D)
    restriction = Maps.maps
    comparison : (Inverting.inclusion W D ∘ restriction) =₁ mapPre l
    comparison = Maps.comparison
    factorization : FunctorLift (Inverting.inclusion W D) (mapPre l)
    factorization = Maps.factorization
    isEquiv : IsEquiv restriction
    isEquiv = Maps.isEquiv (IsLocalization.universal localization D)

  module Factor {D : CAT} (f : MAP C D) (F : Inverts f W) =
    MappingLift W l (Into.factorization D) (Into.isEquiv D) f F

  restriction-reflects : {D : CAT} (f g : MAP T D) → (f ∘ l) =₁ (g ∘ l) → f =₁ g
  restriction-reflects f g α = unnamedIso
    (equiv-reflect (Into.isEquiv _) (nameMap f) (nameMap g)
      (embedding-reflect (Inverting.inclusion W _) (Inverting.inclusion-isEmbedding W _) _ _
        (right ⁻¹ ∙ (nameMapIso α ∙ left))))
    where
    left = mapPre-name l f ∙
      ((Into.comparison _ ▷ nameMap f) ∙
        (comp-assoc (nameMap f) (Into.restriction _) (Inverting.inclusion W _)) ⁻¹)
    right = mapPre-name l g ∙
      ((Into.comparison _ ▷ nameMap g) ∙
        (comp-assoc (nameMap g) (Into.restriction _) (Inverting.inclusion W _)) ⁻¹)
```
