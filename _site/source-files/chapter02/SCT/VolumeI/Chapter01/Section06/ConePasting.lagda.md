# Pasting cones

Pasting retains the selected inner matching and the selected outer matching.
Postcomposing the left leg exposes their composition. Its complete comparison
with the restricted outer cone is the input used by nested insertion.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.ConePasting where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; postWhisker-id₌; preWhisker-id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (postWhisker-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One; comp₌-unitʳ-One; comp₌-inverseʳ-One; postWhisker-inverse; comp₌-inverseˡ-One; inverse-identity; solve-pentagon; preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (pentagon-whiskered)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-action-One; cone-compose; cone-inverse; cone-identification-restrict-One; cone-restrict-assoc)
open import SCT.VolumeI.Chapter01.Section06.Cones

module _ {Γ : Context} where
  postcompose-cone-left : {A B X Z T : CAT Γ} (f : MAP A B) (g : MAP B Z)
    {h : MAP X Z} → Cone (g ∘ f) h T → Cone g h T
  postcompose-cone-left f g s = record
    { left = f ∘ Cone.left s; right = Cone.right s
    ; match = Cone.match s ∙ (comp-assoc (Cone.left s) f g) ⁻¹ }

  postcompose-cone-left-identification : {A B X Z T : CAT Γ}
    (f : MAP A B) (g : MAP B Z) {h : MAP X Z} {s t : Cone (g ∘ f) h T}
    → ConeIdentification₁ s t
    → ConeIdentification₁ (postcompose-cone-left f g s) (postcompose-cone-left f g t)
  postcompose-cone-left-identification f g Φ = record
    { left = f ◁ ConeIdentification₁.left Φ
    ; right = ConeIdentification₁.right Φ
    ; compatible = paste-square₌
        (inverse-square₌ (unconst-sides₌ (postWhisker-comp (ConeIdentification₁.left Φ) f g)))
        (ConeIdentification₁.compatible Φ) }

  postcompose-cone-left-reflect : {A B X Z T : CAT Γ}
    (f : MAP A B) (g : MAP B Z) {h : MAP X Z} (s t : Cone (g ∘ f) h T)
    (α : Cone.left s =₁ Cone.left t) (β : Cone.right s =₁ Cone.right t)
    → SquareCell₌ (g ◁ (f ◁ α)) (h ◁ β)
        (Cone.match (postcompose-cone-left f g s)) (Cone.match (postcompose-cone-left f g t))
    → ConeIdentification₁ s t
  postcompose-cone-left-reflect f g s t α β square = record
    { left = α; right = β
    ; compatible = replace-sides₌
        (inv-comp-right (Cone.match s) (comp-assoc (Cone.left s) f g))
        (inv-comp-right (Cone.match t) (comp-assoc (Cone.left t) f g))
        (paste-square₌ (unconst-sides₌ (postWhisker-comp α f g)) square) }

  postcompose-cone-left-restrict : {A B X Z R T : CAT Γ}
    (f : MAP A B) (g : MAP B Z) {h : MAP X Z}
    (r : MAP R T) (s : Cone (g ∘ f) h T)
    → ConeIdentification₁ (cone-restrict r (postcompose-cone-left f g s))
        (postcompose-cone-left f g (cone-restrict r s))
  postcompose-cone-left-restrict f g {h} r s = record
    { left = comp-assoc r (Cone.left s) f
    ; right = id₌ (Cone.right s ∘ r)
    ; compatible = comp₌-cong ((postWhisker-id₌ h (Cone.right s ∘ r)) ⁻¹) (id₌ source-match) ∙
        ((comp₌-unitˡ-One source-match) ⁻¹ ∙ (source-normal ⁻¹ ∙ target-normal)) }
    where
    original-left = comp-assoc (Cone.left s) f g
    composite-left = comp-assoc r (Cone.left s) (g ∘ f)
    inner-left = comp-assoc r (f ∘ Cone.left s) g
    final-left = comp-assoc (Cone.left s ∘ r) f g
    outer-right = comp-assoc r (Cone.right s) h
    match-at-r = Cone.match s ▷ r
    corner = solve-pentagon final-left composite-left (g ◁ comp-assoc r (Cone.left s) f)
      inner-left (original-left ▷ r) (pentagon-whiskered r (Cone.left s) f g)
    tail = ((original-left ▷ r) ⁻¹) ∙ (inner-left ⁻¹)
    source-match = Cone.match (cone-restrict r (postcompose-cone-left f g s))
    target-match = Cone.match (postcompose-cone-left f g (cone-restrict r s))

    source-normal : source-match =₂ (outer-right ∙ (match-at-r ∙ tail))
    source-normal = comp₌-cong (id₌ outer-right)
      (comp₌-assoc match-at-r ((original-left ▷ r) ⁻¹) (inner-left ⁻¹) ∙
        comp₌-cong
          (comp₌-cong (id₌ match-at-r) (preWhisker-inverse original-left r) ∙
            preWhisker-comp₌ (Cone.match s) (original-left ⁻¹) r)
          (id₌ (inner-left ⁻¹)))

    target-normal : (target-match ∙ (g ◁ comp-assoc r (Cone.left s) f)) =₂
      (outer-right ∙ (match-at-r ∙ tail))
    target-normal = comp₌-cong (id₌ outer-right)
        (comp₌-cong (id₌ match-at-r) (inv-comp-left composite-left tail) ∙
          (comp₌-assoc match-at-r (composite-left ⁻¹) (composite-left ∙ tail) ∙
            comp₌-cong (id₌ (match-at-r ∙ composite-left ⁻¹)) (corner ⁻¹))) ∙
      (comp₌-assoc outer-right (match-at-r ∙ composite-left ⁻¹)
          ((final-left ⁻¹) ∙ (g ◁ comp-assoc r (Cone.left s) f)) ∙
        comp₌-assoc (outer-right ∙ (match-at-r ∙ composite-left ⁻¹)) (final-left ⁻¹)
          (g ◁ comp-assoc r (Cone.left s) f))

  module PasteCones {A B X Z Q : CAT Γ} (f : MAP A B) (g : MAP B Z)
    {h : MAP X Z} (t : Cone g h Q) where
    paste : {T : CAT Γ} → Cone f (Cone.left t) T → Cone (g ∘ f) h T
    paste s = record
      { left = Cone.left s; right = Cone.right t ∘ Cone.right s
      ; match = Cone.match (cone-restrict (Cone.right s) t) ∙
          ((g ◁ Cone.match s) ∙ comp-assoc (Cone.left s) f g) }

    paste-match : {T : CAT Γ} (s : Cone f (Cone.left t) T)
      → Cone.match (postcompose-cone-left f g (paste s)) =₂
          (Cone.match (cone-restrict (Cone.right s) t) ∙ (g ◁ Cone.match s))
    paste-match s = comp-inv-right
        (Cone.match (cone-restrict (Cone.right s) t) ∙ (g ◁ Cone.match s))
        (comp-assoc (Cone.left s) f g) ∙
      comp₌-cong
        ((comp₌-assoc (Cone.match (cone-restrict (Cone.right s) t))
          (g ◁ Cone.match s) (comp-assoc (Cone.left s) f g)) ⁻¹)
        (id₌ ((comp-assoc (Cone.left s) f g) ⁻¹))

    postcompose-paste : {T : CAT Γ} (s : Cone f (Cone.left t) T)
      → ConeIdentification₁ (postcompose-cone-left f g (paste s))
          (cone-restrict (Cone.right s) t)
    postcompose-paste s = record
      { left = Cone.match s; right = id₌ (Cone.right t ∘ Cone.right s)
      ; compatible = comp₌-cong
          ((postWhisker-id₌ h (Cone.right t ∘ Cone.right s)) ⁻¹)
          (id₌ (Cone.match (postcompose-cone-left f g (paste s)))) ∙
        ((comp₌-unitˡ-One (Cone.match (postcompose-cone-left f g (paste s)))) ⁻¹ ∙
          (paste-match s) ⁻¹) }
```




```agda
    paste-identification : {T : CAT Γ} {s s′ : Cone f (Cone.left t) T}
      → ConeIdentification₁ s s′ → ConeIdentification₁ (paste s) (paste s′)
    paste-identification {s = s} {s′} Φ = postcompose-cone-left-reflect f g
      (paste s) (paste s′) (ConeIdentification₁.left Φ) (Cone.right t ◁ ConeIdentification₁.right Φ)
      (replace-sides₌ ((paste-match s) ⁻¹) ((paste-match s′) ⁻¹)
        (paste-square₌ (post-square₌ g (ConeIdentification₁.compatible Φ))
          (ConeIdentification₁.compatible (cone-action-One t (ConeIdentification₁.right Φ)))))
```



```agda
    paste-restrict : {S T : CAT Γ} (r : MAP S T) (s : Cone f (Cone.left t) T)
      → ConeIdentification₁ (cone-restrict r (paste s)) (paste (cone-restrict r s))
    paste-restrict r s = postcompose-cone-left-reflect f g _ _
      (id₌ (Cone.left s ∘ r)) right-associator
      (replace-edges₌ left-normal (postWhisker h ◁ right-normal)
        (ConeIdentification₁.compatible raw))
      where
      right-associator = comp-assoc r (Cone.right s) (Cone.right t)
      restricted-matching = Cone.match (cone-restrict r s)

      raw = cone-compose (cone-inverse (postcompose-paste (cone-restrict r s)))
        (cone-compose (cone-restrict-assoc r (Cone.right s) t)
          (cone-compose (cone-identification-restrict-One r (postcompose-paste s))
            (cone-inverse (postcompose-cone-left-restrict f g r (paste s)))))

      left-normal : (g ◁ ConeIdentification₁.left raw) =₂
        (g ◁ (f ◁ id₌ (Cone.left s ∘ r)))
      left-normal = postWhisker g ◁
        ((postWhisker-id₌ f (Cone.left s ∘ r)) ⁻¹ ∙ comp₌-inverseˡ-One restricted-matching)

      right-normal : ConeIdentification₁.right raw =₂ right-associator
      right-normal = comp₌-unitˡ-One right-associator ∙
        comp₌-cong (inverse-identity (Cone.right t ∘ (Cone.right s ∘ r)))
          (comp₌-unitʳ-One right-associator ∙
            comp₌-cong (id₌ right-associator)
              (comp₌-unitˡ-One (id₌ ((Cone.right t ∘ Cone.right s) ∘ r)) ∙
                comp₌-cong (preWhisker-id₌ (Cone.right t ∘ Cone.right s) r)
                  (inverse-identity ((Cone.right t ∘ Cone.right s) ∘ r))))
```


## Factoring a postcomposed cone

A complete comparison with the supplied outer cone determines the top cone
by its inverse left leg. Pasting that cone recovers the original cone, with
identity left component and the supplied right component.

```agda
    factor-cone : {T : CAT Γ} (s : Cone (g ∘ f) h T) (k : MAP T Q)
      → ConeIdentification₁ (cone-restrict k t) (postcompose-cone-left f g s)
      → Cone f (Cone.left t) T
    factor-cone s k Φ = record
      { left = Cone.left s; right = k; match = (ConeIdentification₁.left Φ) ⁻¹ }

    paste-factor : {T : CAT Γ} (s : Cone (g ∘ f) h T) (k : MAP T Q)
      (Φ : ConeIdentification₁ (cone-restrict k t) (postcompose-cone-left f g s))
      → ConeIdentification₁ (paste (factor-cone s k Φ)) s
    paste-factor s k Φ = postcompose-cone-left-reflect f g _ _
      (id₌ (Cone.left s)) (ConeIdentification₁.right Φ)
      (comp₌-cong (id₌ (h ◁ ConeIdentification₁.right Φ)) ((paste-match (factor-cone s k Φ)) ⁻¹) ∙
        (comp₌-assoc (h ◁ ConeIdentification₁.right Φ) restricted-match (g ◁ left-cell ⁻¹) ∙
          (cancellation ⁻¹ ∙
            (comp₌-unitʳ-One target-match ∙ comp₌-cong (id₌ target-match)
              (postWhisker-id₌ g (f ∘ Cone.left s) ∙
                (postWhisker g ◁ postWhisker-id₌ f (Cone.left s)))))))
      where
      left-cell = ConeIdentification₁.left Φ
      restricted-match = Cone.match (cone-restrict k t)
      target-match = Cone.match (postcompose-cone-left f g s)
      inverse-image = comp₌-inverseʳ-One (g ◁ left-cell) ∙
        comp₌-cong (id₌ (g ◁ left-cell)) (postWhisker-inverse g left-cell)
      cancellation : (((h ◁ ConeIdentification₁.right Φ) ∙ restricted-match) ∙ (g ◁ left-cell ⁻¹)) =₂ target-match
      cancellation = comp₌-unitʳ-One target-match ∙
        (comp₌-cong (id₌ target-match) inverse-image ∙
          (comp₌-assoc target-match (g ◁ left-cell) (g ◁ left-cell ⁻¹) ∙
            comp₌-cong ((ConeIdentification₁.compatible Φ) ⁻¹) (id₌ (g ◁ left-cell ⁻¹))))
```
