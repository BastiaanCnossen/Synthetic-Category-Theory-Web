# Changing the object of an identity family

An identification of object families carries their identity morphisms to
one another. The comparison is obtained by currying the identification of
constant interval diagrams; evaluation retains the original source and
target frames of identity-family.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.IdentityFamilyTransport where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (unconst-sides₌; paste-square₌; replace-sides₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pr₁; pair-β₁)
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle; post-triangle-outer)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (preWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation using (module SectionEvaluation)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Currying using (curry⁼)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (MorphismFamily; MorphismFamilyIdentification; identity-family; evAt; insert; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (retarget-family; family-comparison)

private
  module SectionNaturality {Γ : Context} {X K Y : CAT Γ}
    (pi : MAP K X) (i : MAP X K) (b : (pi ∘ i) =₁ id X)
    {f g : MAP X Y} (p : f =₁ g) where
    module E = SectionEvaluation pi i b
    compatibility : SquareCell₌ ((p ▷ pi) ▷ i) p (E.image f) (E.image g)
    compatibility = paste-square₌ (unconst-sides₌ (post-triangle-outer p pi i b))
      (preWhisker-id-One p)

module IdentityFamilyChange {Γ : Context} {P C : CAT Γ} {f g : MAP P C} (p : f =₁ g) where
  comparison : MorphismFamily.arrow (identity-family f) =₁ MorphismFamily.arrow (identity-family g)
  comparison = curry⁼ (funEval {C = [1]} {D = C}) (funUniversal [1] C) (p ▷ pr₁)

  private
    module At (a : MAP One ([1] {Γ = Γ})) where
      i : MAP P (P × [1])
      i = insert a
      b : (pr₁ ∘ i) =₁ id P
      b = pair-β₁ (id P) (const a)
      module E = SectionEvaluation pr₁ i b
      module N = SectionNaturality pr₁ i b p
      frame : (h : MAP P C) → (evAt a ∘ MorphismFamily.arrow (identity-family h)) =₁ h
      frame h = comp-unitʳ h ∙ ((h ◁ b) ∙
        (comp-assoc i pr₁ h ∙ AtPoint.curry-image a (h ∘ pr₁)))
      normalize : (h : MAP P C) → (E.image h ∙ AtPoint.curry-image a (h ∘ pr₁)) =₂ frame h
      normalize h = comp₌-cong (id₌ (comp-unitʳ h))
        (comp₌-assoc (h ◁ b) (comp-assoc i pr₁ h) (AtPoint.curry-image a (h ∘ pr₁))) ∙
        comp₌-assoc (comp-unitʳ h) (post-triangle h pr₁ i b) (AtPoint.curry-image a (h ∘ pr₁))
      compatibility : (frame g ∙ (evAt a ◁ comparison)) =₂ (p ∙ frame f)
      compatibility = replace-sides₌ (normalize f) (normalize g)
        (paste-square₌ (unconst-sides₌ (AtPoint.curry-square a (p ▷ pr₁))) N.compatibility)

  value : MorphismFamilyIdentification One (retarget-family (identity-family f) p p) (identity-family g)
  value = family-comparison _ _ comparison (At.compatibility zero) (At.compatibility one)
```
