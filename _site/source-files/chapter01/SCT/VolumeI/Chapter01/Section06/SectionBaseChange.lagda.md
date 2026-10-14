# Base change of a section

A section of one cospan arrow pulls back to a section of the opposite cone
projection. Factor its section cone through the supplied universal cone.
The resulting complete beta retains both triangles and the matching square;
inverting its right triangle gives the new section law.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.SectionBaseChange where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (Section)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares

module _ {Γ : Context} where
  module BaseChangeSection {C D E P : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g P) (universal : IsPullback s) (σ : Section f) where
    private
      module U = UniversalCone s universal

    section-cone : Cone f g D
    section-cone = record
      { left = Section.section σ ∘ g
      ; right = id D
      ; match = (comp-unitʳ g) ⁻¹ ∙
          (comp-unitˡ g ∙
            (((Section.section-law σ) ⁻¹ ▷ g) ∙ (comp-assoc g (Section.section σ) f) ⁻¹)) }

    factor : MAP D P
    factor = U.factor section-cone

    cone-law : ConeIdentification₁ (cone-restrict factor s) section-cone
    cone-law = U.β section-cone

    left-triangle : (Cone.left s ∘ factor) =₁ (Section.section σ ∘ g)
    left-triangle = ConeIdentification₁.left cone-law

    right-triangle : (Cone.right s ∘ factor) =₁ id D
    right-triangle = ConeIdentification₁.right cone-law

    compatible : (Cone.match section-cone ∙ (f ◁ left-triangle)) =₂
      ((g ◁ right-triangle) ∙ Cone.match (cone-restrict factor s))
    compatible = ConeIdentification₁.compatible cone-law

    section : Section (Cone.right s)
    section = record { section = factor; section-law = right-triangle ⁻¹ }

  base-change-section : {C D E P : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g P) → IsPullback s → Section f → Section (Cone.right s)
  base-change-section = BaseChangeSection.section
```
