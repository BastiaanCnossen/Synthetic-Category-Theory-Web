# Cones and their identifications

A cone retains its two legs and their specified matching. An identification
of cones has an independent parameter and retains the square between the
matchings. Its higher comparison retains compatibility between these squares.
These are records of data, without a postulated category of cones.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.Cones where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (postWhisker-comp)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses

module _ {Γ : Context} where
  record Cone {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) (T : CAT Γ) : Set m where
    field
      left : MAP T C
      right : MAP T D
      match : (f ∘ left) =₁ (g ∘ right)

  record ConeIdentification (X : CAT Γ) {C D E T : CAT Γ}
    {f : MAP C E} {g : MAP D E} (s t : Cone f g T) : Set m where
    open Terms.Equalities X using (_＝_)
    field
      left : Cone.left s ＝ Cone.left t
      right : Cone.right s ＝ Cone.right t
      compatible : SquareCell₌ (f ◁ left) (g ◁ right)
        (const (Cone.match s)) (const (Cone.match t))

  record ConeIdentificationEquality {X C D E T : CAT Γ}
    {f : MAP C E} {g : MAP D E} {s t : Cone f g T}
    (Φ Ψ : ConeIdentification X s t) : Set m where
    field
      left : ConeIdentification.left Φ =₁ ConeIdentification.left Ψ
      right : ConeIdentification.right Φ =₁ ConeIdentification.right Ψ

    left-boundary :
      (const (Cone.match t) ∙ (f ◁ ConeIdentification.left Φ)) =₁
      (const (Cone.match t) ∙ (f ◁ ConeIdentification.left Ψ))
    left-boundary = comp₌-cong (id₌ (const (Cone.match t))) (postWhisker f ◁ left)

    right-boundary :
      ((g ◁ ConeIdentification.right Φ) ∙ const (Cone.match s)) =₁
      ((g ◁ ConeIdentification.right Ψ) ∙ const (Cone.match s))
    right-boundary = comp₌-cong (postWhisker g ◁ right) (id₌ (const (Cone.match s)))

    field
      compatible : (ConeIdentification.compatible Ψ ∙ left-boundary) =₂
        (right-boundary ∙ ConeIdentification.compatible Φ)
```

## Absolute identifications and the chosen pullback boundary

The pullback axiom uses absolute cone identifications with the original,
unextended matchings. This view retains that exact boundary. Conversion to
or from the family interface explicitly normalizes constant sides at One.
There is no second choice of a cone identification.

```agda
  record ConeIdentification₁ {C D E T : CAT Γ}
    {f : MAP C E} {g : MAP D E} (s t : Cone f g T) : Set m where
    field
      left : Cone.left s =₁ Cone.left t
      right : Cone.right s =₁ Cone.right t
      compatible : SquareCell₌ (f ◁ left) (g ◁ right) (Cone.match s) (Cone.match t)

  cone-identification : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g T} → ConeIdentification₁ s t → ConeIdentification One s t
  cone-identification Φ = record
    { left = ConeIdentification₁.left Φ
    ; right = ConeIdentification₁.right Φ
    ; compatible = const-sides₌ (ConeIdentification₁.compatible Φ) }

  cone-identification-One : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g T} → ConeIdentification One s t → ConeIdentification₁ s t
  cone-identification-One Φ = record
    { left = ConeIdentification.left Φ
    ; right = ConeIdentification.right Φ
    ; compatible = unconst-sides₌ (ConeIdentification.compatible Φ) }

  record ConeIdentification₂ {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g T} (Φ Ψ : ConeIdentification₁ s t) : Set m where
    field
      left : ConeIdentification₁.left Φ =₂ ConeIdentification₁.left Ψ
      right : ConeIdentification₁.right Φ =₂ ConeIdentification₁.right Ψ

    left-boundary :
      (Cone.match t ∙ (f ◁ ConeIdentification₁.left Φ)) =₂
      (Cone.match t ∙ (f ◁ ConeIdentification₁.left Ψ))
    left-boundary = comp₌-cong (id₌ (Cone.match t)) (postWhisker f ◁ left)

    right-boundary :
      ((g ◁ ConeIdentification₁.right Φ) ∙ Cone.match s) =₂
      ((g ◁ ConeIdentification₁.right Ψ) ∙ Cone.match s)
    right-boundary = comp₌-cong (postWhisker g ◁ right) (id₌ (Cone.match s))

    field
      compatible : (ConeIdentification₁.compatible Ψ ∙ left-boundary) =₃
        (right-boundary ∙ ConeIdentification₁.compatible Φ)
```

## Restriction and action on the vertex

Restricting a cone transports its matching along the associators of both
legs. The action on a vertex identification is obtained by pasting those
same associator squares with interchange for the supplied matching.

```agda
  cone-restrict : {C D E S T : CAT Γ} {f : MAP C E} {g : MAP D E}
    → MAP S T → Cone f g T → Cone f g S
  cone-restrict {f = f} {g} r s = record
    { left = Cone.left s ∘ r
    ; right = Cone.right s ∘ r
    ; match = comp-assoc r (Cone.right s) g ∙
        ((Cone.match s ▷ r) ∙ (comp-assoc r (Cone.left s) f) ⁻¹) }

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    cone-action-square : {C D E S T : CAT Γ} {f : MAP C E} {g : MAP D E}
      (s : Cone f g T) {h k : MAP S T} (δ : h ＝ k)
      → SquareCell₌ (f ◁ (Cone.left s ◁ δ)) (g ◁ (Cone.right s ◁ δ))
          (const (Cone.match (cone-restrict h s))) (const (Cone.match (cone-restrict k s)))
    cone-action-square {C} {D} {E} {S} {T} {f = f} {g} s {h} {k} δ = matching-square
      where
      p : MAP T C
      p = Cone.left s
      q : MAP T D
      q = Cone.right s
      ah = comp-assoc h p f
      ak = comp-assoc k p f
      bh = comp-assoc h q g
      bk = comp-assoc k q g
      th = Cone.match s ▷ h
      tk = Cone.match s ▷ k

      normalize : {A B : CAT Γ} {a b c d : MAP A B}
        (β : c =₁ d) (τ : b =₁ c) (α : b =₁ a)
        → (const {P = X} β ∙ (const τ ∙ (const α) ⁻¹)) =₁
          const (β ∙ (τ ∙ α ⁻¹))
      normalize β τ α = const-comp β (τ ∙ α ⁻¹) ∙
        comp₌-cong (id₌ (const β))
          (const-comp τ (α ⁻¹) ∙ comp₌-cong (id₌ (const τ)) ((const-inv α) ⁻¹))

      opaque
        matching-square : SquareCell₌ (f ◁ (p ◁ δ)) (g ◁ (q ◁ δ))
          (const (Cone.match (cone-restrict h s))) (const (Cone.match (cone-restrict k s)))
        matching-square = replace-sides₌ (normalize bh th ah) (normalize bk tk ak)
          (paste-square₌
            (paste-square₌ (inverse-square₌ (postWhisker-comp δ p f))
              (interchange-fixedOuter (Cone.match s) δ))
            (postWhisker-comp δ q g))

```

## Composition and inversion

Pasting the matching squares constructs composition. Inversion reverses
the horizontal direction of a matching square and normalizes its two
whiskered inverse edges.

```agda
  cone-identification-compose : {X C D E T : CAT Γ}
    {f : MAP C E} {g : MAP D E} {s t u : Cone f g T}
    → ConeIdentification X t u → ConeIdentification X s t → ConeIdentification X s u
  cone-identification-compose {f = f} {g} Ψ Φ = record
    { left = ConeIdentification.left Ψ ∙ ConeIdentification.left Φ
    ; right = ConeIdentification.right Ψ ∙ ConeIdentification.right Φ
    ; compatible = replace-edges₌
        ((postWhisker-comp₌ f (ConeIdentification.left Ψ) (ConeIdentification.left Φ)) ⁻¹)
        ((postWhisker-comp₌ g (ConeIdentification.right Ψ) (ConeIdentification.right Φ)) ⁻¹)
        (adjoin-square₌ (ConeIdentification.compatible Φ) (ConeIdentification.compatible Ψ)) }

  cone-identification-inverse : {X C D E T : CAT Γ}
    {f : MAP C E} {g : MAP D E} {s t : Cone f g T}
    → ConeIdentification X s t → ConeIdentification X t s
  cone-identification-inverse {f = f} {g} Φ = record
    { left = (ConeIdentification.left Φ) ⁻¹
    ; right = (ConeIdentification.right Φ) ⁻¹
    ; compatible = replace-edges₌
        ((postWhisker-inverse f (ConeIdentification.left Φ)) ⁻¹)
        ((postWhisker-inverse g (ConeIdentification.right Φ)) ⁻¹)
        (transpose-square₌ (inverse-square₌ (transpose-square₌ (ConeIdentification.compatible Φ)))) }
```
