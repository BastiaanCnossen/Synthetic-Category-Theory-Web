# Pasting complete framed corners

Two complete corner comparisons sharing one selected leg determine a
comparison between their other legs. The supplied comparison of common
legs is used explicitly. Adjusting a comparison retains its full square
while exposing the selected leg heads at the next producer boundary.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.FramedConePasting where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-right; inv-comp-left)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (replace-sides₌; replace-edges₌; transpose-square₌; inverse-square₌; adjoin-square₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (inverse-inverse; inverse-composite)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-swap-identification)

module _ {Γ : Context} where
  unframe-source : {P A B C : CAT Γ} {f : MAP A C} {g : MAP B C}
    {u : MAP P A} {v : MAP P B} {z : MAP P C} {t : Cone f g P}
    (p : (f ∘ u) =₁ z) (q : (g ∘ v) =₁ z)
    (K : (f ∘ u) =₁ (g ∘ v)) → (q ∙ K) =₂ p
    → ConeIdentification₁ (framed-cone f g u v p q) t
    → ConeIdentification₁ (record { left = u; right = v; match = K }) t
  unframe-source p q K law given = record
    { left = ConeIdentification₁.left given; right = ConeIdentification₁.right given
    ; compatible = replace-sides₌
        ((comp₌-cong (id₌ (q ⁻¹)) law ∙ (inv-comp-left q K) ⁻¹) ⁻¹)
        (id₌ _) (ConeIdentification₁.compatible given) }

  adjust : {P A B C : CAT Γ} {f : MAP A C} {g : MAP B C}
    {s t : Cone f g P} (given : ConeIdentification₁ s t)
    (left : Cone.left s =₁ Cone.left t) (right : Cone.right s =₁ Cone.right t)
    → ConeIdentification₁.left given =₂ left
    → ConeIdentification₁.right given =₂ right
    → ConeIdentification₁ s t
  adjust {f = f} {g} given left right left-image right-image = record
    { left = left; right = right
    ; compatible = replace-edges₌ (postWhisker f ◁ left-image)
        (postWhisker g ◁ right-image) (ConeIdentification₁.compatible given) }

  inverse-quotient : {P C : CAT Γ} {x y z : MAP P C}
    (p : x =₁ z) (q : y =₁ z) → ((q ⁻¹ ∙ p) ⁻¹) =₂ (p ⁻¹ ∙ q)
  inverse-quotient p q = comp₌-cong (id₌ (p ⁻¹)) (inverse-inverse q) ∙
    inverse-composite (q ⁻¹) p

  quotient-through : {P C : CAT Γ} {x y z w : MAP P C}
    (p : x =₁ w) (q : y =₁ w) (r : z =₁ w)
    → ((r ⁻¹ ∙ p) ∙ (q ⁻¹ ∙ p) ⁻¹) =₂ (r ⁻¹ ∙ q)
  quotient-through p q r = comp₌-cong (comp-inv-right (r ⁻¹) p) (id₌ q) ∙
    ((comp₌-assoc (r ⁻¹ ∙ p) (p ⁻¹) q) ⁻¹ ∙
      comp₌-cong (id₌ (r ⁻¹ ∙ p)) (inverse-quotient p q))

module ThroughCommon {Γ : Context} {P A B D C : CAT Γ}
  {f : MAP A C} {g : MAP B C} {h : MAP D C}
  {l l′ : MAP P A} {m m′ : MAP P B} {n n′ : MAP P D} {z z′ : MAP P C}
  (p : (f ∘ l) =₁ z) (q : (g ∘ m) =₁ z) (r : (h ∘ n) =₁ z)
  (p′ : (f ∘ l′) =₁ z′) (q′ : (g ∘ m′) =₁ z′) (r′ : (h ∘ n′) =₁ z′)
  (first : ConeIdentification₁ (framed-cone f g l m p q) (framed-cone f g l′ m′ p′ q′))
  (second : ConeIdentification₁ (framed-cone f h l n p r) (framed-cone f h l′ n′ p′ r′))
  (same : ConeIdentification₁.left second =₂ ConeIdentification₁.left first) where
  left : m =₁ m′
  left = ConeIdentification₁.right first
  right : n =₁ n′
  right = ConeIdentification₁.right second

  comparison : ConeIdentification₁ (framed-cone g h m n q r) (framed-cone g h m′ n′ q′ r′)
  comparison = record
    { left = left; right = right
    ; compatible = transpose-square₌ (replace-edges₌ (quotient-through p q r) (quotient-through p′ q′ r′)
        (adjoin-square₌
          (transpose-square₌ (inverse-square₌ (ConeIdentification₁.compatible first)))
          (transpose-square₌ (replace-edges₌ (postWhisker f ◁ same) (id₌ (h ◁ right))
            (ConeIdentification₁.compatible second))))) }

module _ {Γ : Context} where
  swap-framed : {P A B C : CAT Γ} {f : MAP A C} {g : MAP B C}
    {l l′ : MAP P A} {r r′ : MAP P B} {z z′ : MAP P C}
    (p : (f ∘ l) =₁ z) (q : (g ∘ r) =₁ z)
    (p′ : (f ∘ l′) =₁ z′) (q′ : (g ∘ r′) =₁ z′)
    → ConeIdentification₁ (framed-cone f g l r p q) (framed-cone f g l′ r′ p′ q′)
    → ConeIdentification₁ (framed-cone g f r l q p) (framed-cone g f r′ l′ q′ p′)
  swap-framed p q p′ q′ given = record
    { left = ConeIdentification₁.right given; right = ConeIdentification₁.left given
    ; compatible = replace-sides₌ (inverse-quotient p q) (inverse-quotient p′ q′)
        (ConeIdentification₁.compatible (cone-swap-identification given)) }
```
