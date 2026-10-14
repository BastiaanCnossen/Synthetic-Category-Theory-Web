# Comparing two localizations

The factorization property supplies functors in both directions over the
original category. Restricting their composites gives the identities;
reflection after restriction therefore gives an equivalence compatible
with the localization maps. This supplies the comparison in
`exercise:Uniqueness_Of_Localizations`.

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

module SCT.VolumeI.Chapter03.Section03.LocalizationUniqueness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
  using (CAT; MAP; IsEquiv; _∘_; _=₁_; id; _⁻¹; _∙_; _◁_; comp-unitˡ; comp-assoc)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.LocalizationUniversal 𝒯 M ℱ P I E S Q R using (module Universal)

module Uniqueness (L : SubcategoryAxiom) {C : CAT} (W : MorphismCollection C)
  (source target : WithSubcategories.Localization L W) where
  open WithSubcategories L
  module Source = Localization source
  module Target = Localization target
  module SourceUP = Universal L W Source.functor Source.isLocalization using (module Factor; restriction-reflects)
  module TargetUP = Universal L W Target.functor Target.isLocalization using (module Factor; restriction-reflects)
  module Forward = SourceUP.Factor Target.functor (IsLocalization.inverts Target.isLocalization) using (factor; comparison)
  module Backward = TargetUP.Factor Source.functor (IsLocalization.inverts Source.isLocalization) using (factor; comparison)

  forward : MAP Source.category Target.category
  forward = Forward.factor
  backward : MAP Target.category Source.category
  backward = Backward.factor

  over-source : (forward ∘ Source.functor) =₁ Target.functor
  over-source = Forward.comparison
  over-target : (backward ∘ Target.functor) =₁ Source.functor
  over-target = Backward.comparison

  section-comparison : (backward ∘ forward) =₁ id Source.category
  section-comparison = SourceUP.restriction-reflects _ _
    ((comp-unitˡ Source.functor) ⁻¹ ∙
      (over-target ∙ ((backward ◁ over-source) ∙ comp-assoc Source.functor forward backward)))

  retraction-comparison : (forward ∘ backward) =₁ id Target.category
  retraction-comparison = TargetUP.restriction-reflects _ _
    ((comp-unitˡ Target.functor) ⁻¹ ∙
      (over-source ∙ ((forward ◁ over-target) ∙ comp-assoc Target.functor backward forward)))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record { inverse = backward
    ; sectionIso = section-comparison ⁻¹ ; retractionIso = retraction-comparison ⁻¹ }
```
