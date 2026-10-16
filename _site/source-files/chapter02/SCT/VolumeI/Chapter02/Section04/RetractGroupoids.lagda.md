# Retracts of groupoids

A section of the existing constant-diagram functor transfers along a
retraction of categories. Its section first postcomposes with the inclusion,
then uses the given section, then the retraction. The section triangle follows
from the native constant-diagram naturality and postcomposition laws.

For the walking morphism, the existing source-evaluation retraction supplies
the other inverse. Thus groupoids are closed under retracts without an extra
compatibility condition on the given retraction triangle.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section04.RetractGroupoids where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (Section)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality
  using (funPost; funPost-comp; funPost-cong; funPost-id)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (constantArrow)
open import SCT.VolumeI.Chapter02.Section04.Groupoids
  using (IsGroupoid; groupoid-to-identity-section; identity-section-to-groupoid)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure using (constant-natural)

module _ {Γ : Context} where
  constant-section-retract : (I : CAT Γ) {X Y : CAT Γ}
    (s : MAP Y X) (r : MAP X Y) → (r ∘ s) =₁ id Y
    → Section (constantArrow I X) → Section (constantArrow I Y)
  constant-section-retract I {X} {Y} s r ε given = record
    { section = transferred
    ; section-law = counit ⁻¹ }
    where
      post-s : MAP (Fun I Y) (Fun I X)
      post-s = funPost {C = I} s
      post-r : MAP (Fun I X) (Fun I Y)
      post-r = funPost {C = I} r
      j : MAP (Fun I X) X
      j = Section.section given
      restricted-section : MAP (Fun I Y) X
      restricted-section = j ∘ post-s
      transferred : MAP (Fun I Y) Y
      transferred = r ∘ restricted-section

      naturality : (constantArrow I Y ∘ transferred)
        =₁ (post-r ∘ (constantArrow I X ∘ restricted-section))
      naturality = comp-assoc restricted-section (constantArrow I X) post-r ∙
        (((constant-natural I {C = X} {D = Y} r) ⁻¹ ▷ restricted-section) ∙
          (comp-assoc restricted-section r (constantArrow I Y)) ⁻¹)

      section-image : (constantArrow I X ∘ restricted-section) =₁ post-s
      section-image = comp-unitˡ post-s ∙
        (((Section.section-law given) ⁻¹ ▷ post-s) ∙
          (comp-assoc post-s j (constantArrow I X)) ⁻¹)

      counit : (constantArrow I Y ∘ transferred) =₁ id (Fun I Y)
      counit = funPost-id I Y ∙
        (funPost-cong {C = I} ε ∙
          (funPost-comp {A = I} s r ∙ ((post-r ◁ section-image) ∙ naturality)))

  retract-isGroupoid : {X Y : CAT Γ} (s : MAP Y X) (r : MAP X Y)
    → (r ∘ s) =₁ id Y → IsGroupoid X → IsGroupoid Y
  retract-isGroupoid {X} {Y} s r ε given = identity-section-to-groupoid {C = Y}
    (constant-section-retract [1] {X = X} {Y = Y} s r ε
      (groupoid-to-identity-section {C = X} given))
```
