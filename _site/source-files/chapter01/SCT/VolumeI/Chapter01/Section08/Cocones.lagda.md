# Cocones with their specified matching

A cocone on a fixed span retains its two outgoing legs and their matching.
Its identification families have an independent categorical parameter and
retain the square between the matchings. The existing square between functors
supplies the cocone of a commutative square; no second square record is used.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section08.Cocones where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Squares using (Square)

module _ {Γ : Context} where
  record Cocone {A B C : CAT Γ} (u : MAP A B) (l : MAP A C) (T : CAT Γ) : Set m where
    field
      left : MAP B T
      right : MAP C T
      match : (left ∘ u) =₁ (right ∘ l)

  square-cocone : {A B C D : CAT Γ} {l : MAP A C} {r : MAP B D}
    (s : Square l r) → Cocone (Square.source-map s) l D
  square-cocone {r = r} s = record
    { left = r ; right = Square.target-map s ; match = Square.cell s }

  record CoconeIdentification (X : CAT Γ) {A B C T : CAT Γ}
    {u : MAP A B} {l : MAP A C} (s t : Cocone u l T) : Set m where
    open Terms.Equalities X using (_＝_)
    field
      left : Cocone.left s ＝ Cocone.left t
      right : Cocone.right s ＝ Cocone.right t
      compatible : SquareCell₌ (left ▷ u) (right ▷ l)
        (const (Cocone.match s)) (const (Cocone.match t))

  record CoconeIdentificationEquality {X A B C T : CAT Γ}
    {u : MAP A B} {l : MAP A C} {s t : Cocone u l T}
    (Φ Ψ : CoconeIdentification X s t) : Set m where
    field
      left : CoconeIdentification.left Φ =₁ CoconeIdentification.left Ψ
      right : CoconeIdentification.right Φ =₁ CoconeIdentification.right Ψ

    left-boundary :
      (const (Cocone.match t) ∙ (CoconeIdentification.left Φ ▷ u)) =₁
      (const (Cocone.match t) ∙ (CoconeIdentification.left Ψ ▷ u))
    left-boundary = comp₌-cong (id₌ (const (Cocone.match t))) (preWhisker u ◁ left)

    right-boundary :
      ((CoconeIdentification.right Φ ▷ l) ∙ const (Cocone.match s)) =₁
      ((CoconeIdentification.right Ψ ▷ l) ∙ const (Cocone.match s))
    right-boundary = comp₌-cong (preWhisker l ◁ right) (id₌ (const (Cocone.match s)))

    field
      compatible : (CoconeIdentification.compatible Ψ ∙ left-boundary) =₂
        (right-boundary ∙ CoconeIdentification.compatible Φ)
```

Individual identifications retain the original, unextended matchings.
Conversion to the family interface at One normalizes the constant sides.
Pasting and inversion use the existing identification-square operations.

```agda
  record CoconeIdentification₁ {A B C T : CAT Γ}
    {u : MAP A B} {l : MAP A C} (s t : Cocone u l T) : Set m where
    field
      left : Cocone.left s =₁ Cocone.left t
      right : Cocone.right s =₁ Cocone.right t
      compatible : SquareCell₌ (left ▷ u) (right ▷ l) (Cocone.match s) (Cocone.match t)

  cocone-identification : {A B C T : CAT Γ} {u : MAP A B} {l : MAP A C}
    {s t : Cocone u l T} → CoconeIdentification₁ s t → CoconeIdentification One s t
  cocone-identification Φ = record
    { left = CoconeIdentification₁.left Φ
    ; right = CoconeIdentification₁.right Φ
    ; compatible = const-sides₌ (CoconeIdentification₁.compatible Φ) }

  cocone-identification-One : {A B C T : CAT Γ} {u : MAP A B} {l : MAP A C}
    {s t : Cocone u l T} → CoconeIdentification One s t → CoconeIdentification₁ s t
  cocone-identification-One Φ = record
    { left = CoconeIdentification.left Φ
    ; right = CoconeIdentification.right Φ
    ; compatible = unconst-sides₌ (CoconeIdentification.compatible Φ) }

  cocone-identification-compose : {X A B C T : CAT Γ}
    {u : MAP A B} {l : MAP A C} {s t v : Cocone u l T}
    → CoconeIdentification X t v → CoconeIdentification X s t → CoconeIdentification X s v
  cocone-identification-compose {u = u} {l} Ψ Φ = record
    { left = CoconeIdentification.left Ψ ∙ CoconeIdentification.left Φ
    ; right = CoconeIdentification.right Ψ ∙ CoconeIdentification.right Φ
    ; compatible = replace-edges₌
        ((preWhisker-comp₌ (CoconeIdentification.left Ψ) (CoconeIdentification.left Φ) u) ⁻¹)
        ((preWhisker-comp₌ (CoconeIdentification.right Ψ) (CoconeIdentification.right Φ) l) ⁻¹)
        (adjoin-square₌ (CoconeIdentification.compatible Φ) (CoconeIdentification.compatible Ψ)) }

  cocone-identification-inverse : {X A B C T : CAT Γ}
    {u : MAP A B} {l : MAP A C} {s t : Cocone u l T}
    → CoconeIdentification X s t → CoconeIdentification X t s
  cocone-identification-inverse {u = u} {l} Φ = record
    { left = (CoconeIdentification.left Φ) ⁻¹
    ; right = (CoconeIdentification.right Φ) ⁻¹
    ; compatible = replace-edges₌
        ((preWhisker-inverse (CoconeIdentification.left Φ) u) ⁻¹)
        ((preWhisker-inverse (CoconeIdentification.right Φ) l) ⁻¹)
        (transpose-square₌ (inverse-square₌ (transpose-square₌ (CoconeIdentification.compatible Φ)))) }

  cocone-postcompose : {A B C T R : CAT Γ} {u : MAP A B} {l : MAP A C}
    → MAP T R → Cocone u l T → Cocone u l R
  cocone-postcompose {u = u} {l} h s = record
    { left = h ∘ Cocone.left s ; right = h ∘ Cocone.right s
    ; match = (comp-assoc l (Cocone.right s) h) ⁻¹ ∙
        ((h ◁ Cocone.match s) ∙ comp-assoc u (Cocone.left s) h) }
```
