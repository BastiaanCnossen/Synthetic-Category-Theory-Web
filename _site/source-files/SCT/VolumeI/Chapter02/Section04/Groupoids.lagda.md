# Recognizing groupoids by constant arrows

The lifting condition in `def:Groupoid` is tested on arbitrary absolute
categories of parameters. Applying it to the universal arrow gives a
section of `isoArrow`. Rezk then gives a section of `identityArrow`,
whose retraction is endpoint evaluation. These are the four conditions
of `prop:Characterization_Groupoids`.

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

module SCT.VolumeI.Chapter02.Section04.Groupoids
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open Rezk 𝒯 M ℱ P I E public
open RezkAxiom R

IsGroupoid : CAT → Set m
IsGroupoid C = IsEquiv (identityArrow {C})

record AllArrowsInvertible (C : CAT) : Set (c ⊔ m) where
  field
    lift-arrow : {Γ : CAT} (f : MAP Γ (Ar C)) → IsoLift f

lifting-to-section : {C : CAT} → AllArrowsInvertible C → Section (isoArrow {C})
lifting-to-section {C} h = record
  { section = IsoLift.lift universal
  ; comparison = IsoLift.comparison universal }
  where universal = AllArrowsInvertible.lift-arrow h (id (Ar C))

section-to-lifting : {C : CAT} → Section (isoArrow {C}) → AllArrowsInvertible C
section-to-lifting h = record { lift-arrow = λ f → record
  { lift = Section.section h ∘ f
  ; comparison = comp-unitˡ f ∙ ((Section.comparison h ▷ f) ∙
      (comp-assoc f (Section.section h) isoArrow) ⁻¹) } }

iso-section-to-identity-section : {C : CAT} →
  Section (isoArrow {C}) → Section (identityArrow {C})
iso-section-to-identity-section {C} h = record
  { section = j ∘ s
  ; comparison = Section.comparison h ∙
      ((isoArrow ◁ (comp-unitˡ s ∙ ((ε ▷ s) ∙ (comp-assoc s j identityIso) ⁻¹))) ∙
      (comp-assoc (j ∘ s) identityIso isoArrow ∙
        (identityIso-arrow ⁻¹ ▷ (j ∘ s)))) }
  where
  s = Section.section h
  j = IsEquiv.inverse (rezk-isEquiv C)
  ε = (IsEquiv.retractionIso (rezk-isEquiv C)) ⁻¹

identity-section-to-iso-section : {C : CAT} →
  Section (identityArrow {C}) → Section (isoArrow {C})
identity-section-to-iso-section h = record
  { section = identityIso ∘ Section.section h
  ; comparison = Section.comparison h ∙
      ((identityIso-arrow ▷ Section.section h) ∙
        (comp-assoc (Section.section h) identityIso isoArrow) ⁻¹) }

identity-section-to-groupoid : {C : CAT} → Section (identityArrow {C}) → IsGroupoid C
identity-section-to-groupoid s = section-retraction-isEquiv s
  (record { retraction = ev₀ ; comparison = identity-source ⁻¹ })

groupoid-to-identity-section : {C : CAT} → IsGroupoid C → Section (identityArrow {C})
groupoid-to-identity-section = equiv-section

groupoid-to-lifting : {C : CAT} → IsGroupoid C → AllArrowsInvertible C
groupoid-to-lifting e = section-to-lifting (identity-section-to-iso-section (equiv-section e))

lifting-to-groupoid : {C : CAT} → AllArrowsInvertible C → IsGroupoid C
lifting-to-groupoid h = identity-section-to-groupoid
  (iso-section-to-identity-section (lifting-to-section h))
```
