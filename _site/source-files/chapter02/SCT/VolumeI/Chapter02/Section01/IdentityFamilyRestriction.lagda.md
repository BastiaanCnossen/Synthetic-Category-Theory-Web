# Restricting the identity morphism family

The identity of an object family commutes with changing its parameter.
The comparison is reflected from the original curried diagram beta laws.
Both endpoint equations use the actual uncurry parameter law and the
specified insertion section square, so the original identity-family frames
are retained.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.IdentityFamilyRestriction where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle; post-square-cell; restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation using (module SectionEvaluation)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; funCurry-β; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong; evaluate⁼-absolute; evaluate-restrict)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; evAt; insert; identity-family; MorphismFamily; MorphismFamilyIdentification; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (restrict-family; family-comparison)
open import SCT.VolumeI.Chapter02.Section01.RestrictedDiagramEvaluation using (module RestrictedDiagramEvaluation)
open import SCT.VolumeI.Chapter02.Section01.InsertionSectionEvaluation using (module InsertionSectionEvaluation)

open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection using (module ReflectedEndpoint)

module IdentityFamilyRestriction {Γ : Context} {P Q C : CAT Γ}
  (f : MAP P C) (r : MAP Q P) where
  private
    H : MAP (P × [1]) C
    H = f ∘ pr₁
    Hnew : MAP (Q × [1]) C
    Hnew = (f ∘ r) ∘ pr₁
    h : MAP P (Ar C)
    h = MorphismFamily.arrow (identity-family f)
    k : MAP Q (Ar C)
    k = MorphismFamily.arrow (identity-family (f ∘ r))
    J : MAP (Q × [1]) (P × [1])
    J = productMap r (id [1])
    beta = funCurry-β H
    beta-new = funCurry-β Hnew
    projection = pair-β₁ (r ∘ pr₁) (id [1] ∘ pr₂)
    diagram = post-square-cell f pr₁ r pr₁ J projection
    representation = (beta ▷ J) ∙ evaluate-restrict (funEval {C = [1]} {D = C}) h r
    theta = diagram ∙ representation
    module Chosen = ReflectedEndpoint (h ∘ r) k Hnew beta-new theta

  comparison : (h ∘ r) =₁ k
  comparison = Chosen.comparison

  private
    module Frame {T : CAT Γ} (a : MAP One ([1] {Γ = Γ})) (g : MAP T C) where
      i : MAP T (T × [1])
      i = insert a
      b = pair-β₁ (id T) (const {P = T} a)
      module E = SectionEvaluation pr₁ i b
      value : (evAt a ∘ MorphismFamily.arrow (identity-family g)) =₁ g
      value = comp-unitʳ g ∙ ((g ◁ b) ∙
        (comp-assoc i pr₁ g ∙ AtPoint.curry-image a (g ∘ pr₁)))
      normalize : (E.image g ∙ AtPoint.curry-image a (g ∘ pr₁)) =₂ value
      normalize = comp₌-cong (id₌ (comp-unitʳ g))
        (comp₌-assoc (g ◁ b) (comp-assoc i pr₁ g) (AtPoint.curry-image a (g ∘ pr₁))) ∙
        comp₌-assoc (comp-unitʳ g) (post-triangle g pr₁ i b) (AtPoint.curry-image a (g ∘ pr₁))

    module At (a : MAP One ([1] {Γ = Γ})) where
      module Old = Frame a f
      module New = Frame a (f ∘ r)
      module Rep = RestrictedDiagramEvaluation a h H beta r
      module Section = InsertionSectionEvaluation a r f
      i : MAP Q (Q × [1])
      i = insert a
      output = New.E.image (f ∘ r)
      old-output = Old.E.image f
      A = comp-assoc r h (evAt a)
      d = diagram ▷ i
      action = evAt a ◁ comparison
      old-point = AtPoint.curry-image a H
      new-point = AtPoint.curry-image a Hnew
      through-representation : (New.value ∙ action) =₂ (output ∙ (d ∙ Rep.point))
      through-representation = comp₌-cong (id₌ output)
          (comp₌-assoc d (representation ▷ i) (AtPoint.uncurry-image a (h ∘ r))) ∙
        (comp₌-cong (id₌ output)
          (comp₌-cong (preWhisker-comp₌ diagram representation i) (id₌ (AtPoint.uncurry-image a (h ∘ r)))) ∙
          (comp₌-cong (id₌ output) (Chosen.endpoint a) ∙
            (comp₌-assoc output new-point action ∙
              comp₌-cong (New.normalize ⁻¹) (id₌ action))))
      restricted : ((output ∙ (d ∙ Rep.point)) ∙ A) =₂ (Old.value ▷ r)
      restricted = (preWhisker r ◁ Old.normalize) ∙
        (((preWhisker-comp₌ old-output old-point r) ⁻¹) ∙
          (comp₌-cong Section.compatibility (id₌ (old-point ▷ r)) ∙
            (((comp₌-assoc output (d ∙ Section.route) (old-point ▷ r)) ⁻¹) ∙
              (comp₌-cong (id₌ output) ((comp₌-assoc d Section.route (old-point ▷ r)) ⁻¹) ∙
                (comp₌-cong (id₌ output) (comp₌-cong (id₌ d) Rep.compatibility) ∙
                  (comp₌-cong (id₌ output) (comp₌-assoc d Rep.point A) ∙
                    comp₌-assoc output (d ∙ Rep.point) A))))))
      compatible : (New.value ∙ action) =₂ restrict-triangle (evAt a) h Old.value r
      compatible = comp₌-cong
          (restricted ∙ comp₌-cong through-representation (id₌ A)) (id₌ (A ⁻¹)) ∙
        (comp-inv-right (New.value ∙ action) A) ⁻¹

  value : MorphismFamilyIdentification One (restrict-family (identity-family f) r) (identity-family (f ∘ r))
  value = family-comparison _ _ comparison (At.compatible zero) (At.compatible one)
```
