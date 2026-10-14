# Cones framed by a common object

Two legs identified with one common object determine their matching by
composing one frame with the inverse of the other. Comparisons of both
frames give a comparison of these cones. Restriction retains the actual
associators in the cone matching, and changing the common object cancels
the same endpoint identification on the two frames.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.ConeFramings where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; postWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (paste-square₌; inverse-square₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (CompatibleOver)
open import SCT.VolumeI.Chapter01.Section06.Cones

module _ {Γ : Context} where
  framed-cone : {P A B C : CAT Γ} (f : MAP A C) (g : MAP B C)
    (u : MAP P A) (v : MAP P B) {x : MAP P C}
    → (f ∘ u) =₁ x → (g ∘ v) =₁ x → Cone f g P
  framed-cone f g u v a b = record { left = u; right = v; match = b ⁻¹ ∙ a }

  matching-comparison : {P A B C : CAT Γ} {f : MAP A C} {g : MAP B C}
    {u : MAP P A} {v : MAP P B} (a b : (f ∘ u) =₁ (g ∘ v)) → a =₂ b
    → ConeIdentification₁ (record { left = u; right = v; match = a })
        (record { left = u; right = v; match = b })
  matching-comparison {f = f} {g} {u} {v} a b given = record
    { left = id₌ u; right = id₌ v
    ; compatible = comp₌-cong ((postWhisker-id₌ g v) ⁻¹) (id₌ a) ∙
        ((comp₌-unitˡ-One a) ⁻¹ ∙ (given ⁻¹ ∙
          (comp₌-unitʳ-One b ∙ comp₌-cong (id₌ b) (postWhisker-id₌ f u)))) }

  framed-cone-comparison : {P A B C : CAT Γ} (f : MAP A C) (g : MAP B C)
    {u u′ : MAP P A} {v v′ : MAP P B} {x : MAP P C}
    (a : (f ∘ u) =₁ x) (b : (g ∘ v) =₁ x)
    (a′ : (f ∘ u′) =₁ x) (b′ : (g ∘ v′) =₁ x)
    (left : u =₁ u′) (right : v =₁ v′)
    → CompatibleOver f a a′ left → CompatibleOver g b b′ right
    → ConeIdentification₁ (framed-cone f g u v a b) (framed-cone f g u′ v′ a′ b′)
  framed-cone-comparison f g a b a′ b′ left right first second = record
    { left = left; right = right
    ; compatible = paste-square₌ ((comp₌-unitˡ-One a) ⁻¹ ∙ first)
        (inverse-square₌ ((comp₌-unitˡ-One b) ⁻¹ ∙ second)) }

  module FramedConeRestriction {P Q A B C : CAT Γ} (f : MAP A C) (g : MAP B C)
    (u : MAP P A) (v : MAP P B) {x : MAP P C}
    (a : (f ∘ u) =₁ x) (b : (g ∘ v) =₁ x) (r : MAP Q P) where
    private
      left-assoc = comp-assoc r u f
      right-assoc = comp-assoc r v g
      first = a ▷ r
      second = b ▷ r
    original : Cone f g P
    original = framed-cone f g u v a b
    restricted : Cone f g Q
    restricted = framed-cone f g (u ∘ r) (v ∘ r)
      (restrict-triangle f u a r) (restrict-triangle g v b r)
    private
      quotient-image : (Cone.match original ▷ r) =₂ (second ⁻¹ ∙ first)
      quotient-image = comp₌-cong (preWhisker-inverse b r) (id₌ first) ∙
        preWhisker-comp₌ (b ⁻¹) a r
      inverse-frame : ((second ∙ right-assoc ⁻¹) ⁻¹) =₂ (right-assoc ∙ second ⁻¹)
      inverse-frame = comp₌-cong (inverse-inverse right-assoc) (id₌ (second ⁻¹)) ∙
        inverse-composite second (right-assoc ⁻¹)
    matching : Cone.match restricted =₂ Cone.match (cone-restrict r original)
    matching = comp₌-cong (id₌ right-assoc)
      (comp₌-cong (quotient-image ⁻¹) (id₌ (left-assoc ⁻¹))) ∙
      (reassociateFour right-assoc (second ⁻¹) first (left-assoc ⁻¹) ∙
        comp₌-cong inverse-frame (id₌ (first ∙ left-assoc ⁻¹)))
    comparison : ConeIdentification₁ restricted (cone-restrict r original)
    comparison = matching-comparison _ _ matching

  module FramedConeEndpointChange {P A B C : CAT Γ} (f : MAP A C) (g : MAP B C)
    (u : MAP P A) (v : MAP P B) {x y : MAP P C}
    (a : (f ∘ u) =₁ x) (b : (g ∘ v) =₁ x) (p : x =₁ y) where
    original : Cone f g P
    original = framed-cone f g u v a b
    changed : Cone f g P
    changed = framed-cone f g u v (p ∙ a) (p ∙ b)
    matching : Cone.match changed =₂ Cone.match original
    matching = comp₌-cong (id₌ (b ⁻¹)) (inv-comp-left p a) ∙
      (comp₌-assoc (b ⁻¹) (p ⁻¹) (p ∙ a) ∙
        comp₌-cong (inverse-composite p b) (id₌ (p ∙ a)))
    comparison : ConeIdentification₁ changed original
    comparison = matching-comparison _ _ matching
```
