# Reflecting an identification of represented arrow diagrams

Two arrow families representing the same interval diagram have a specified
comparison obtained by reflection. Its value at every point is the pasting
of the two original representation triangles. Identity restriction and unit
triangles share this computation, including its literal endpoint images.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; comp-inv-left; preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong; evaluate⁼-absolute)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; insert; evAt; module AtPoint)

module ReflectedEndpoint {Γ : Context} {P C : CAT Γ}
  (h k : MAP P (Ar C)) (H : MAP (P × [1]) C)
  (β : funUncurry k =₁ H) (θ : funUncurry h =₁ H) where
  private
    e = funEval {C = [1]} {D = C}
    raw = β ⁻¹ ∙ θ
  comparison : h =₁ k
  comparison = reflect e (funUniversal [1] C) h k raw
  image : evaluate-cong e comparison =₂ raw
  image = reflect-β-One e (funUniversal [1] C) h k raw

  endpoint : (x : MAP One ([1] {Γ = Γ}))
    → (((β ▷ insert x) ∙ AtPoint.uncurry-image x k) ∙ (evAt x ◁ comparison)) =₂
        ((θ ▷ insert x) ∙ AtPoint.uncurry-image x h)
  endpoint x = comp₌-cong normalized (id₌ (AtPoint.uncurry-image x h)) ∙
    ((comp₌-assoc (β ▷ i) (raw ▷ i) (AtPoint.uncurry-image x h)) ⁻¹ ∙
      (comp₌-cong (id₌ (β ▷ i)) square ∙
        comp₌-assoc (β ▷ i) (AtPoint.uncurry-image x k) (evAt x ◁ comparison)))
    where
      i = insert {P = P} x
      normalized : ((β ▷ i) ∙ (raw ▷ i)) =₂ (θ ▷ i)
      normalized = comp-inv-left (β ▷ i) (θ ▷ i) ∙
        comp₌-cong (id₌ (β ▷ i))
          (comp₌-cong (preWhisker-inverse β i) (id₌ (θ ▷ i)) ∙
            preWhisker-comp₌ (β ⁻¹) θ i)
      square : (AtPoint.uncurry-image x k ∙ (evAt x ◁ comparison)) =₂
        ((raw ▷ i) ∙ AtPoint.uncurry-image x h)
      square = comp₌-cong
        (preWhisker i ◁ (image ∙ evaluate⁼-absolute e comparison))
        (id₌ (AtPoint.uncurry-image x h)) ∙
        unconst-sides₌ (AtPoint.uncurry-square x comparison)
```
