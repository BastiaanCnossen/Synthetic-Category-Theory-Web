# Functors preserve the chosen identity families

Postcomposing a constant interval diagram gives the constant diagram on
the image object family. Reflection compares their curried arrows. The
native point equation for postcomposition and evaluation along the insertion
section prove its two endpoint equations for the existing functor action.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.IdentityFamilyPostcomposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; comp₌-cong; preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pr₁; pair-β₁)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation using (module SectionEvaluation)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry; funCurry-β; funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-uncurry)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; insert; evAt; module AtPoint; MorphismFamily; MorphismFamilyIdentification; identity-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (evAt-post; map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationPostcomposition using (module PointPostcomposition)

module IdentityImage {Γ : Context} {P C D : CAT Γ} (F : MAP C D) (f : MAP P C) where
  private
    pi : MAP (P × [1]) P
    pi = pr₁
    h : MAP P (Ar C)
    h = funCurry (f ∘ pi)
    k : MAP P (Ar D)
    k = funCurry ((F ∘ f) ∘ pi)
    H = funPost F ∘ h
    beta = funCurry-β (f ∘ pi)
    beta′ = funCurry-β ((F ∘ f) ∘ pi)
    eta = (comp-assoc pi f F) ⁻¹ ∙ (F ◁ beta)
    u = funPost-uncurry F h
    theta = eta ∙ u
    module Lift = ReflectedEndpoint H k ((F ∘ f) ∘ pi) beta′ theta

    module At (a : MAP One ([1] {Γ = Γ})) where
      i : MAP P (P × [1])
      i = insert a
      b : (pi ∘ i) =₁ id P
      b = pair-β₁ (id P) (const a)
      module E = SectionEvaluation pi i b
      module S = E.Compared f (funUncurry h) beta F
      module Point = PointPostcomposition a F h

      frame : {Z : CAT Γ} (g : MAP P Z) → (evAt a ∘ funCurry (g ∘ pi)) =₁ g
      frame g = comp-unitʳ g ∙ ((g ◁ b) ∙
        (comp-assoc i pi g ∙ AtPoint.curry-image a (g ∘ pi)))

      normalize : {Z : CAT Γ} (g : MAP P Z)
        → (E.image g ∙ AtPoint.curry-image a (g ∘ pi)) =₂ frame g
      normalize g = comp₌-cong (id₌ (comp-unitʳ g))
        (comp₌-assoc (g ◁ b) (comp-assoc i pi g) (AtPoint.curry-image a (g ∘ pi))) ∙
          comp₌-assoc (comp-unitʳ g) (post-triangle g pi i b) (AtPoint.curry-image a (g ∘ pi))

      input-tail = E.image f ∙ (beta ▷ i)
      module Image = Point.Framed input-tail
      mu = AtPoint.uncurry-image a H
      source-normal : (input-tail ∙ AtPoint.uncurry-image a h) =₂ frame f
      source-normal = normalize f ∙
        comp₌-assoc (E.image f) (beta ▷ i) (AtPoint.uncurry-image a h)

      mapped-frame : (evAt a ∘ H) =₁ (F ∘ f)
      mapped-frame = (F ◁ frame f) ∙
        (comp-assoc h (evAt a) F ∙
          ((evAt-post a F ▷ h) ∙ (comp-assoc h (funPost F) (evAt a)) ⁻¹))

      reflected : (frame (F ∘ f) ∙ (evAt a ◁ Lift.comparison)) =₂
        (E.image (F ∘ f) ∙ ((theta ▷ i) ∙ mu))
      reflected = comp₌-cong (id₌ (E.image (F ∘ f))) (Lift.endpoint a) ∙
        (comp₌-assoc (E.image (F ∘ f)) (AtPoint.curry-image a ((F ∘ f) ∘ pi))
          (evAt a ◁ Lift.comparison) ∙
          comp₌-cong ((normalize (F ∘ f)) ⁻¹) (id₌ (evAt a ◁ Lift.comparison)))

      diagram-frame : (E.image (F ∘ f) ∙ ((theta ▷ i) ∙ mu)) =₂
        (((F ◁ input-tail) ∙ comp-assoc i (funUncurry h) F) ∙ ((u ▷ i) ∙ mu))
      diagram-frame = comp₌-cong S.compatibility (id₌ ((u ▷ i) ∙ mu)) ∙
        ((comp₌-assoc (E.image (F ∘ f)) (eta ▷ i) ((u ▷ i) ∙ mu)) ⁻¹ ∙
          (comp₌-cong (id₌ (E.image (F ∘ f))) (comp₌-assoc (eta ▷ i) (u ▷ i) mu) ∙
            comp₌-cong (id₌ (E.image (F ∘ f)))
              (comp₌-cong (preWhisker-comp₌ eta u i) (id₌ mu))))

      compatible : (frame (F ∘ f) ∙ (evAt a ◁ Lift.comparison)) =₂ mapped-frame
      compatible = comp₌-cong (postWhisker F ◁ source-normal)
        (id₌ (comp-assoc h (evAt a) F ∙
          ((evAt-post a F ▷ h) ∙ (comp-assoc h (funPost F) (evAt a)) ⁻¹))) ∙
        (Image.frame-image ∙ (diagram-frame ∙ reflected))

  value : MorphismFamilyIdentification One
    (map-morphism-family F (identity-family f)) (identity-family (F ∘ f))
  value = family-comparison _ _ Lift.comparison (At.compatible zero) (At.compatible one)

post-identity-family : {Γ : Context} {P C D : CAT Γ} (F : MAP C D) (f : MAP P C)
  → MorphismFamilyIdentification One
      (map-morphism-family F (identity-family f)) (identity-family (F ∘ f))
post-identity-family = IdentityImage.value
```
