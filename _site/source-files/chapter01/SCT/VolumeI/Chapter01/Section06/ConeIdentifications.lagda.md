# Encoding and restricting cone identifications

The two leg identification animae map into the identification anima between
opposite corners. Their maps are the specified composites with the two cone
matchings. Encoding and decoding transport along their evaluation triangles.
The higher decoding law retains the square between matching compatibilities.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.ConeIdentifications where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (whisker-mixed)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (transport-square; cancel-endpoint-changes)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (whisker-mixed-One; pentagon-whiskered-right; right-unitor-comp)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle-inner; restrict-triangle; restrict-triangle-id; restrict-triangle-assoc)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (comp₌-evaluate-natural-One; const-comp-evaluate; comp-const-evaluate;
    const-comp-evaluate-natural; comp-const-evaluate-natural)
open import SCT.VolumeI.Chapter01.Section06.Cones

module _ {Γ : Context} where
  private
    constant-restriction-square : {X K C : CAT Γ} (x : Obj-abs C)
      {r s : MAP X K} (δ : r =₁ s)
      → SquareCell₌ (const x ◁ δ) (id₌ (const {P = X} x)) (const-pre x r) (const-pre x s)
    constant-restriction-square {X} {K} x {r} {s} δ =
      replace-edges₌ (id₌ (const x ◁ δ)) (postWhisker-id₌ x (terminate X))
        (unconst-sides₌
          (post-triangle-inner x (terminate K) δ (id₌ (terminate X))
            (terminal-identification (terminate K ∘ r) (terminate X))
            (terminal-identification (terminate K ∘ s) (terminate X))
            (const-sides₌ (terminal-unique₂ _ _))))

  module IdentificationBoundary {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s t : Cone f g T) where
    Left : CAT Γ
    Left = Equal (Cone.left s) (Cone.left t)
    Right : CAT Γ
    Right = Equal (Cone.right s) (Cone.right t)
    Middle : CAT Γ
    Middle = Equal (f ∘ Cone.left s) (g ∘ Cone.right t)

    left-map : MAP Left Middle
    left-map = const (Cone.match t) ∙ postWhisker f
    right-map : MAP Right Middle
    right-map = postWhisker g ∙ const (Cone.match s)

    left-evaluation : {X : CAT Γ} (α : MAP X Left)
      → (left-map ∘ α) =₁ (const (Cone.match t) ∙ (f ◁ α))
    left-evaluation α = comp₌-evaluate-One (const (Cone.match t)) (postWhisker f) α
      (const-pre (Cone.match t) α) (id₌ (f ◁ α))

    right-evaluation : {X : CAT Γ} (β : MAP X Right)
      → (right-map ∘ β) =₁ ((g ◁ β) ∙ const (Cone.match s))
    right-evaluation β = comp₌-evaluate-One (postWhisker g) (const (Cone.match s)) β
      (id₌ (g ◁ β)) (const-pre (Cone.match s) β)

    encode : {X : CAT Γ} → ConeIdentification X s t → Cone left-map right-map X
    encode Φ = record
      { left = ConeIdentification.left Φ
      ; right = ConeIdentification.right Φ
      ; match = (right-evaluation (ConeIdentification.right Φ)) ⁻¹ ∙
          (ConeIdentification.compatible Φ ∙ left-evaluation (ConeIdentification.left Φ)) }

    decode : {X : CAT Γ} → Cone left-map right-map X → ConeIdentification X s t
    decode z = record
      { left = Cone.left z
      ; right = Cone.right z
      ; compatible = right-evaluation (Cone.right z) ∙
          (Cone.match z ∙ (left-evaluation (Cone.left z)) ⁻¹) }

    opaque
      decode-identification : {X : CAT Γ} {z z′ : Cone left-map right-map X}
        → ConeIdentification₁ z z′ → ConeIdentificationEquality (decode z) (decode z′)
      decode-identification {z = z} {z′} Ω = record
        { left = ConeIdentification₁.left Ω
        ; right = ConeIdentification₁.right Ω
        ; compatible = transport-square
            (left-evaluation (Cone.left z)) (left-evaluation (Cone.left z′))
            (right-evaluation (Cone.right z)) (right-evaluation (Cone.right z′))
            (Cone.match z) (Cone.match z′)
            (left-map ◁ ConeIdentification₁.left Ω) (right-map ◁ ConeIdentification₁.right Ω)
            (comp₌-cong (id₌ (const (Cone.match t))) (postWhisker f ◁ ConeIdentification₁.left Ω))
            (comp₌-cong (postWhisker g ◁ ConeIdentification₁.right Ω) (id₌ (const (Cone.match s))))
            (comp₌-evaluate-natural-One (const (Cone.match t)) (postWhisker f)
              (ConeIdentification₁.left Ω)
              (const-pre (Cone.match t) (Cone.left z)) (const-pre (Cone.match t) (Cone.left z′))
              (id₌ _) (id₌ _) (id₌ (const (Cone.match t))) (postWhisker f ◁ ConeIdentification₁.left Ω)
              (constant-restriction-square (Cone.match t) (ConeIdentification₁.left Ω))
              (unconst-sides₌ (identity-square₌ (postWhisker f ◁ ConeIdentification₁.left Ω))))
            (comp₌-evaluate-natural-One (postWhisker g) (const (Cone.match s))
              (ConeIdentification₁.right Ω) (id₌ _) (id₌ _)
              (const-pre (Cone.match s) (Cone.right z)) (const-pre (Cone.match s) (Cone.right z′))
              (postWhisker g ◁ ConeIdentification₁.right Ω) (id₌ (const (Cone.match s)))
              (unconst-sides₌ (identity-square₌ (postWhisker g ◁ ConeIdentification₁.right Ω)))
              (constant-restriction-square (Cone.match s) (ConeIdentification₁.right Ω)))
            (ConeIdentification₁.compatible Ω) }

      decode-into : {X : CAT Γ} (z : Cone left-map right-map X) (Φ : ConeIdentification X s t)
        → ConeIdentification₁ z (encode Φ) → ConeIdentificationEquality (decode z) Φ
      decode-into z Φ Ω = record
        { left = ConeIdentificationEquality.left Ξ
        ; right = ConeIdentificationEquality.right Ξ
        ; compatible = ConeIdentificationEquality.compatible Ξ ∙
            comp₌-cong ((cancel-endpoint-changes
              (left-evaluation (ConeIdentification.left Φ))
              (right-evaluation (ConeIdentification.right Φ)) (ConeIdentification.compatible Φ)) ⁻¹)
              (id₌ (comp₌-cong (id₌ (const (Cone.match t)))
                (postWhisker f ◁ ConeIdentificationEquality.left Ξ))) }
        where
        Ξ : ConeIdentificationEquality (decode z) (decode (encode Φ))
        Ξ = decode-identification Ω

```

The absolute view keeps the original evaluation triangles and the original
encoding route used by the pullback restriction axiom. At One these triangles
evaluate constant functors, rather than treating them as their values.

```agda
    left-evaluation-One : (α : Obj-abs Left)
      → (left-map ∘ α) =₁ (Cone.match t ∙ (f ◁ α))
    left-evaluation-One α = const-comp-evaluate (Cone.match t) (postWhisker f) α

    right-evaluation-One : (β : Obj-abs Right)
      → (right-map ∘ β) =₁ ((g ◁ β) ∙ Cone.match s)
    right-evaluation-One β = comp-const-evaluate (postWhisker g) (Cone.match s) β

    encode-One : ConeIdentification₁ s t → Cone left-map right-map One
    encode-One Φ = record
      { left = ConeIdentification₁.left Φ
      ; right = ConeIdentification₁.right Φ
      ; match = (right-evaluation-One (ConeIdentification₁.right Φ)) ⁻¹ ∙
          (ConeIdentification₁.compatible Φ ∙ left-evaluation-One (ConeIdentification₁.left Φ)) }

    decode-One : Cone left-map right-map One → ConeIdentification₁ s t
    decode-One z = record
      { left = Cone.left z
      ; right = Cone.right z
      ; compatible = right-evaluation-One (Cone.right z) ∙
          (Cone.match z ∙ (left-evaluation-One (Cone.left z)) ⁻¹) }

    opaque
      decode-identification-One : {z z′ : Cone left-map right-map One}
        → ConeIdentification₁ z z′ → ConeIdentification₂ (decode-One z) (decode-One z′)
      decode-identification-One {z} {z′} Ω = record
        { left = ConeIdentification₁.left Ω
        ; right = ConeIdentification₁.right Ω
        ; compatible = transport-square
            (left-evaluation-One (Cone.left z)) (left-evaluation-One (Cone.left z′))
            (right-evaluation-One (Cone.right z)) (right-evaluation-One (Cone.right z′))
            (Cone.match z) (Cone.match z′)
            (left-map ◁ ConeIdentification₁.left Ω) (right-map ◁ ConeIdentification₁.right Ω)
            (comp₌-cong (id₌ (Cone.match t)) (postWhisker f ◁ ConeIdentification₁.left Ω))
            (comp₌-cong (postWhisker g ◁ ConeIdentification₁.right Ω) (id₌ (Cone.match s)))
            (const-comp-evaluate-natural (Cone.match t) (postWhisker f) (ConeIdentification₁.left Ω))
            (comp-const-evaluate-natural (postWhisker g) (Cone.match s) (ConeIdentification₁.right Ω))
            (ConeIdentification₁.compatible Ω) }

      decode-into-One : (z : Cone left-map right-map One) (Φ : ConeIdentification₁ s t)
        → ConeIdentification₁ z (encode-One Φ) → ConeIdentification₂ (decode-One z) Φ
      decode-into-One z Φ Ω = record
        { left = ConeIdentification₂.left Ξ
        ; right = ConeIdentification₂.right Ξ
        ; compatible = ConeIdentification₂.compatible Ξ ∙
            comp₌-cong ((cancel-endpoint-changes
              (left-evaluation-One (ConeIdentification₁.left Φ))
              (right-evaluation-One (ConeIdentification₁.right Φ))
              (ConeIdentification₁.compatible Φ)) ⁻¹)
              (id₌ (comp₌-cong (id₌ (Cone.match t)) (postWhisker f ◁ ConeIdentification₂.left Ξ))) }
        where
        Ξ : ConeIdentification₂ (decode-One z) (decode-One (encode-One Φ))
        Ξ = decode-identification-One Ω
```

## The actual action cone

The action on the vertex has the two postwhiskering functors as its legs.
Its matching is the family action evaluated at the identity family, with
the same unitor normalizations and evaluation triangles. Factoring this
particular cone will define the pullback restriction functor.

```agda
  module ConeAction {C D E S T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) (h k : MAP S T) where
    module Boundary = IdentificationBoundary (cone-restrict h s) (cone-restrict k s)
    p : MAP T C
    p = Cone.left s
    q : MAP T D
    q = Cone.right s

    left-evaluation : (Boundary.left-map ∘ postWhisker p) =₁
      (const (Cone.match (cone-restrict k s)) ∙ (f ◁ postWhisker p))
    left-evaluation = Boundary.left-evaluation (postWhisker p)

    right-evaluation : (Boundary.right-map ∘ postWhisker q) =₁
      ((g ◁ postWhisker q) ∙ const (Cone.match (cone-restrict h s)))
    right-evaluation = Boundary.right-evaluation (postWhisker q)

    matching : (Boundary.left-map ∘ postWhisker p) =₁ (Boundary.right-map ∘ postWhisker q)
    matching = right-evaluation ⁻¹ ∙
      (comp₌-cong (postWhisker g ◁ comp-unitʳ (postWhisker q)) (id₌ _) ∙
      (cone-action-square s (id (Equal h k)) ∙
      ((comp₌-cong (id₌ _) (postWhisker f ◁ comp-unitʳ (postWhisker p))) ⁻¹ ∙
        left-evaluation)))

    identification-cone : Cone Boundary.left-map Boundary.right-map (Equal h k)
    identification-cone = record { left = postWhisker p ; right = postWhisker q ; match = matching }

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    cone-action : {C D E S T : CAT Γ} {f : MAP C E} {g : MAP D E}
      (s : Cone f g T) {h k : MAP S T} → h ＝ k
      → ConeIdentification X (cone-restrict h s) (cone-restrict k s)
    cone-action s {h} {k} δ = ConeAction.Boundary.decode s h k
      (cone-restrict δ (ConeAction.identification-cone s h k))

  cone-action-One : {C D E S T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) {h k : MAP S T} → h =₁ k
    → ConeIdentification₁ (cone-restrict h s) (cone-restrict k s)
  cone-action-One s {h} {k} δ = ConeAction.Boundary.decode-One s h k
    (cone-restrict δ (ConeAction.identification-cone s h k))
```

## Restriction of matching squares

Restriction acts on both legs of a cone identification. Transporting the
restricted matching square along the two associators preserves its full
compatibility. Absolute composition and inversion explicitly pass through
the family interface.

```agda
  cone-compose : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t u : Cone f g T} → ConeIdentification₁ t u → ConeIdentification₁ s t
    → ConeIdentification₁ s u
  cone-compose Ψ Φ = cone-identification-One
    (cone-identification-compose (cone-identification Ψ) (cone-identification Φ))

  cone-inverse : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g T} → ConeIdentification₁ s t → ConeIdentification₁ t s
  cone-inverse Φ = cone-identification-One (cone-identification-inverse (cone-identification Φ))

  cone-identification-restrict-One : {C D E S T : CAT Γ}
    {f : MAP C E} {g : MAP D E} {s t : Cone f g T}
    (r : MAP S T) → ConeIdentification₁ s t
    → ConeIdentification₁ (cone-restrict r s) (cone-restrict r t)
  cone-identification-restrict-One {f = f} {g} {s} {t} r Φ = record
    { left = ConeIdentification₁.left Φ ▷ r
    ; right = ConeIdentification₁.right Φ ▷ r
    ; compatible = transport-square
        (comp-assoc r (Cone.left s) f) (comp-assoc r (Cone.left t) f)
        (comp-assoc r (Cone.right s) g) (comp-assoc r (Cone.right t) g)
        (Cone.match s ▷ r) (Cone.match t ▷ r)
        ((f ◁ ConeIdentification₁.left Φ) ▷ r) ((g ◁ ConeIdentification₁.right Φ) ▷ r)
        (f ◁ (ConeIdentification₁.left Φ ▷ r)) (g ◁ (ConeIdentification₁.right Φ ▷ r))
        (whisker-mixed-One (ConeIdentification₁.left Φ) r f)
        (whisker-mixed-One (ConeIdentification₁.right Φ) r g)
        (pre-square₌ r (ConeIdentification₁.compatible Φ)) }
```

## Successive restriction

The associativity square is the pasting of the corresponding triangle
square with the associator pentagon on the right leg. Restriction's unit
law is the triangle unit law followed by the right-unitor comparison.

```agda
  cone-restrict-assoc : {C D E Q R T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (r : MAP Q R) (u : MAP R T) (s : Cone f g T)
    → ConeIdentification₁ (cone-restrict r (cone-restrict u s)) (cone-restrict (u ∘ r) s)
  cone-restrict-assoc {f = f} {g} r u s = record
    { left = comp-assoc r u (Cone.left s)
    ; right = comp-assoc r u (Cone.right s)
    ; compatible = replace-sides₌ normalize (id₌ _)
        (paste-square₌
          (restrict-triangle-assoc f (Cone.left s) (Cone.match s) u r)
          (pentagon-whiskered-right r u (Cone.right s) g)) }
    where
    outer-associator = comp-assoc u (Cone.right s) g
    restricted-associator = comp-assoc r (Cone.right s ∘ u) g
    whiskered-associator = outer-associator ▷ r
    whiskered-triangle = restrict-triangle f (Cone.left s) (Cone.match s) u ▷ r
    inverse-associator = (comp-assoc r (Cone.left s ∘ u) f) ⁻¹

    normalize : ((restricted-associator ∙ whiskered-associator) ∙ (whiskered-triangle ∙ inverse-associator)) =₂ Cone.match (cone-restrict r (cone-restrict u s))
    normalize = comp₌-cong (id₌ restricted-associator)
        (comp₌-cong ((preWhisker-comp₌ outer-associator (restrict-triangle f (Cone.left s) (Cone.match s) u) r) ⁻¹)
            (id₌ inverse-associator) ∙ (comp₌-assoc whiskered-associator whiskered-triangle inverse-associator) ⁻¹) ∙
      comp₌-assoc restricted-associator whiskered-associator (whiskered-triangle ∙ inverse-associator)

  cone-restrict-id : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) → ConeIdentification₁ (cone-restrict (id T) s) s
  cone-restrict-id {f = f} {g} s = record
    { left = comp-unitʳ (Cone.left s)
    ; right = comp-unitʳ (Cone.right s)
    ; compatible = comp₌-assoc (g ◁ comp-unitʳ (Cone.right s))
        (comp-assoc (id _) (Cone.right s) g) tail ∙
        (comp₌-cong (right-unitor-comp (Cone.right s) g) (id₌ tail) ∙
          (restrict-triangle-id f (Cone.left s) (g ∘ Cone.right s) (Cone.match s)) ⁻¹) }
    where
    tail = restrict-triangle f (Cone.left s) (Cone.match s) (id _)
```
