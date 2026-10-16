# Complete corner transport with shared leg comparisons

The input is a complete target cone with its two chosen vertex frames.
The two edge comparisons and the common vertex comparison are selected once.
Their full endpoint computations produce a comparison of cones whose legs
are literally those selected edge comparisons. This supporting calculation
does not assert the six geometric specializations or their common diagonal.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.FramedConeTransport where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; comp-inv-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-left)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone)

module Corner {Γ : Context} {P A B C : CAT Γ}
  (f : MAP A C) (g : MAP B C)
  (target : Cone f g P)
  {x y : MAP P C} {u : MAP P A} {v : MAP P B}
  (source-left : (f ∘ u) =₁ x) (source-right : (g ∘ v) =₁ x)
  (target-left : (f ∘ Cone.left target) =₁ y)
  (target-right : (g ∘ Cone.right target) =₁ y)
  (target-junction : (target-right ∙ Cone.match target) =₂ target-left)
  (left : u =₁ Cone.left target) (right : v =₁ Cone.right target)
  (vertex : x =₁ y)
  (left-image : (target-left ∙ (f ◁ left)) =₂ (vertex ∙ source-left))
  (right-image : (target-right ∙ (g ◁ right)) =₂ (vertex ∙ source-right)) where

  source : Cone f g P
  source = framed-cone f g u v source-left source-right

  private
    source-matching = Cone.match source
    target-matching = Cone.match target
    left-endpoint = f ◁ left
    right-endpoint = g ◁ right

    left-normal : (target-right ∙ (target-matching ∙ left-endpoint)) =₂
      (vertex ∙ source-left)
    left-normal = left-image ∙
      (comp₌-cong target-junction (id₌ left-endpoint) ∙
        (comp₌-assoc target-right target-matching left-endpoint) ⁻¹)

    right-normal : (target-right ∙ (right-endpoint ∙ source-matching)) =₂
      (vertex ∙ source-left)
    right-normal = comp₌-cong (id₌ vertex) (comp-inv-left source-right source-left) ∙
      (comp₌-assoc vertex source-right source-matching ∙
        (comp₌-cong right-image (id₌ source-matching) ∙
          (comp₌-assoc target-right right-endpoint source-matching) ⁻¹))

  compatible : (target-matching ∙ (f ◁ left)) =₂
    ((g ◁ right) ∙ Cone.match source)
  compatible = cancel-left target-right ((right-normal ⁻¹) ∙ left-normal)

  comparison : ConeIdentification₁ source target
  comparison = record { left = left; right = right; compatible = compatible }
```
