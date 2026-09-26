# Specified comparisons for geometric realization

Geometric realization acts on functors by localization functoriality.
Its identity, composition, and square comparisons are lifted together
with prescribed restriction witnesses. In particular, realizing a square
retains its chosen commutativity identification.

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

module SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.RealizationComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (Square)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.LocalizationFunctoriality 𝒯 M ℱ P I E S Q R using (module Induced)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationIdentificationLifting 𝒯 M ℱ P I E S Q R
  using (module Identification)
open import SCT.VolumeI.Chapter03.Section04.GeometricRealization 𝒯 M ℱ P I E S Q R using (module Realization)

module RealizationAction (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L) where
  module Geom = Realization L Z using (category; localization; universal; chosen; preserves-all)

  abstract
    action : {C D : CAT} → MAP C D → MAP (Geom.category C) (Geom.category D)
    action {C} {D} f = Induced.functor L (allMorphisms C) (allMorphisms D)
      (Geom.chosen C) (Geom.chosen D) f (Geom.preserves-all f)

    naturality : {C D : CAT} (f : MAP C D) →
      (action f ∘ Geom.localization C) =₁ (Geom.localization D ∘ f)
    naturality {C} {D} f = Induced.comparison L (allMorphisms C) (allMorphisms D)
      (Geom.chosen C) (Geom.chosen D) f (Geom.preserves-all f)

  composite-naturality : {B C D : CAT} (f : MAP B C) (g : MAP C D) →
    ((action g ∘ action f) ∘ Geom.localization B) =₁ (Geom.localization D ∘ (g ∘ f))
  composite-naturality {B} {C} {D} f g = comp-assoc f g (Geom.localization D) ∙
    ((naturality g ▷ f) ∙
      ((comp-assoc f (Geom.localization C) (action g)) ⁻¹ ∙
        ((action g ◁ naturality f) ∙ comp-assoc (Geom.localization B) (action f) (action g))))

  module Identity (C : CAT) where
    prescribed : (action (id C) ∘ Geom.localization C) =₁ (id (Geom.category C) ∘ Geom.localization C)
    prescribed = (comp-unitˡ (Geom.localization C)) ⁻¹ ∙
      (comp-unitʳ (Geom.localization C) ∙ naturality (id C))
    module Lifted = Identification.Between L (allMorphisms C) (Geom.localization C) (Geom.universal C)
      (action (id C)) (id (Geom.category C)) prescribed
    identity : action (id C) =₁ id (Geom.category C)
    identity = Lifted.lift
    image : (identity ▷ Geom.localization C) =₂ prescribed
    image = Lifted.image

  module CompositeFunctor {B C D : CAT} (f : MAP B C) (g : MAP C D) where
    prescribed : ((action g ∘ action f) ∘ Geom.localization B) =₁
      (action (g ∘ f) ∘ Geom.localization B)
    prescribed = (naturality (g ∘ f)) ⁻¹ ∙ composite-naturality f g
    module Lifted = Identification.Between L (allMorphisms B) (Geom.localization B) (Geom.universal B)
      (action g ∘ action f) (action (g ∘ f)) prescribed
    composite-comparison : (action g ∘ action f) =₁ action (g ∘ f)
    composite-comparison = Lifted.lift
    image : (composite-comparison ▷ Geom.localization B) =₂ prescribed
    image = Lifted.image

  module SquareImage {A B C D : CAT} {u : MAP A B} {l : MAP A C}
    {r : MAP B D} {v : MAP C D} (square : Square u l r v) where
    prescribed : ((action r ∘ action u) ∘ Geom.localization A) =₁
      ((action v ∘ action l) ∘ Geom.localization A)
    prescribed = (composite-naturality l v) ⁻¹ ∙
      ((Geom.localization D ◁ Square.commute square) ∙ composite-naturality u r)
    module Lifted = Identification.Between L (allMorphisms A) (Geom.localization A) (Geom.universal A)
      (action r ∘ action u) (action v ∘ action l) prescribed

    abstract
      value : Square (action u) (action l) (action r) (action v)
      value = record { commute = Lifted.lift }

      matching-image : (Square.commute value ▷ Geom.localization A) =₂ prescribed
      matching-image = Lifted.image
```

`SquareImage.value` constructs the realized square with a specified
comparison to the original matching. This module does not yet prove that
it preserves a pushout square. No triangle or pentagon law for the chosen
identity and composition comparisons is asserted here.
