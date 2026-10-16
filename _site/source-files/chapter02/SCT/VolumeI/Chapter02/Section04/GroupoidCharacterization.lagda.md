# The four groupoid conditions

Every arrow family is invertible when it factors through the actual
isomorphism-arrow functor, for an arbitrary categorical parameter. Applying
this condition to the universal arrow gives a section of that functor;
restricting a section recovers the factorization of each family.

The actual identity-isomorphism functor compares the isomorphism-arrow
functor with the constant-arrow functor. Its Rezk inverse transports a
section in the other direction. Together with the constant-arrow section
criterion, these constructions give all four conditions of
prop:Characterization_Groupoids. No anima-recognition condition is used.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section04.GroupoidCharacterization where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (Section)
open import SCT.VolumeI.Chapter01.Section03.Factorizations using (Factorization; factor; triangle)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors using (functor-over)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; identityArrow)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms
  using (Iso; isoArrow; identityIso; identityIso-arrow)
open import SCT.VolumeI.Chapter02.Section03.RezkAxiom using (rezk-isEquiv)
open import SCT.VolumeI.Chapter02.Section04.Groupoids
  using (IsGroupoid; identity-section-to-groupoid; groupoid-to-identity-section)

module _ {Γ : Context} where
  AllArrowsInvertible : CAT Γ → Set (c ⊔ m)
  AllArrowsInvertible C = {P : CAT Γ} → (f : MAP P (Ar C)) → Factorization (isoArrow C) f

  lifting-to-section : {C : CAT Γ} → AllArrowsInvertible C → Section (isoArrow C)
  lifting-to-section {C} given = record
    { section = factor universal
    ; section-law = (triangle universal) ⁻¹ }
    where
      universal : Factorization (isoArrow C) (id (Ar C))
      universal = given {P = Ar C} (id (Ar C))

  section-to-lifting : {C : CAT Γ} → Section (isoArrow C) → AllArrowsInvertible C
  section-to-lifting {C} given f = functor-over (Section.section given ∘ f)
    (comp-unitˡ f ∙ (((Section.section-law given) ⁻¹ ▷ f) ∙
      (comp-assoc f (Section.section given) (isoArrow C)) ⁻¹))

  identity-section-to-iso-section : {C : CAT Γ}
    → Section (identityArrow {C = C}) → Section (isoArrow C)
  identity-section-to-iso-section {C} given = record
    { section = identityIso C ∘ s
    ; section-law = comp-assoc s (identityIso C) (isoArrow C) ∙
        (((identityIso-arrow C ▷ s) ⁻¹) ∙ Section.section-law given) }
    where
      s : MAP (Ar C) C
      s = Section.section given

  iso-section-to-identity-section : {C : CAT Γ}
    → Section (isoArrow C) → Section (identityArrow {C = C})
  iso-section-to-identity-section {C} given = record
    { section = j ∘ s
    ; section-law = comp-assoc s j (identityArrow {C = C}) ∙
        (((inverse-image ▷ s) ⁻¹) ∙ Section.section-law given) }
    where
      s : MAP (Ar C) (Iso C)
      s = Section.section given
      j : MAP (Iso C) C
      j = IsEquiv.inverse (rezk-isEquiv C)
      inverse-image : (identityArrow {C = C} ∘ j) =₁ isoArrow C
      inverse-image = comp-unitʳ (isoArrow C) ∙
        (((isoArrow C) ◁ ((IsEquiv.right-inverse-law (rezk-isEquiv C)) ⁻¹)) ∙
          (comp-assoc j (identityIso C) (isoArrow C) ∙
            (identityIso-arrow C ▷ j) ⁻¹))

  groupoid-to-lifting : {C : CAT Γ} → IsGroupoid C → AllArrowsInvertible C
  groupoid-to-lifting given =
    section-to-lifting (identity-section-to-iso-section (groupoid-to-identity-section given))

  lifting-to-groupoid : {C : CAT Γ} → AllArrowsInvertible C → IsGroupoid C
  lifting-to-groupoid given =
    identity-section-to-groupoid (iso-section-to-identity-section (lifting-to-section given))
```
