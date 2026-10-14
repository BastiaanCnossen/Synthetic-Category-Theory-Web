# Changing a cospan arrow

Changing the right arrow by a supplied identification transports each cone
with matching exactly the composite of the restricted arrow identification
and the supplied matching. The complete matching square is transported by
pasting with interchange.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.ConeTransport where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; postWhisker-id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitʳ-One; comp₌-unitˡ-One; comp₌-inverseˡ-One; comp₌-inverseʳ-One; preWhisker-inverse; inverse-composite; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (preWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; changeEndpoints-to-square; square-to-changeEndpoints)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-compose)
open import SCT.VolumeI.Chapter01.Section06.Cones

module _ {Γ : Context} where
  cone-change-right : {C D E T : CAT Γ} {f : MAP C E} {g g′ : MAP D E}
    → g =₁ g′ → Cone f g T → Cone f g′ T
  cone-change-right δ s = record
    { left = Cone.left s
    ; right = Cone.right s
    ; match = (δ ▷ Cone.right s) ∙ Cone.match s }

  cone-change-right-identification : {C D E T : CAT Γ}
    {f : MAP C E} {g g′ : MAP D E} (δ : g =₁ g′)
    {s t : Cone f g T} → ConeIdentification₁ s t
    → ConeIdentification₁ (cone-change-right δ s) (cone-change-right δ t)
  cone-change-right-identification δ Φ = record
    { left = ConeIdentification₁.left Φ
    ; right = ConeIdentification₁.right Φ
    ; compatible = paste-square₌ (ConeIdentification₁.compatible Φ)
        (unconst-sides₌ (interchange-fixedOuter δ (ConeIdentification₁.right Φ))) }
```


## Retargeting a specified matching

A comparison of matching witnesses changes the matching while retaining both
legs. The resulting cone identification includes the unit comparisons of
postwhiskering, so its full compatibility is explicit.

```agda
  cone-retarget-match : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) → (f ∘ Cone.left s) =₁ (g ∘ Cone.right s) → Cone f g T
  cone-retarget-match s ν = record
    { left = Cone.left s; right = Cone.right s; match = ν }

  cone-retarget-match-identification : {C D E T : CAT Γ}
    {f : MAP C E} {g : MAP D E} (s : Cone f g T)
    (ν : (f ∘ Cone.left s) =₁ (g ∘ Cone.right s))
    → Cone.match s =₂ ν → ConeIdentification₁ s (cone-retarget-match s ν)
  cone-retarget-match-identification {f = f} {g} s ν q = record
    { left = id₌ (Cone.left s)
    ; right = id₌ (Cone.right s)
    ; compatible = normalize-right ⁻¹ ∙ (q ⁻¹ ∙ normalize-left) }
    where
    normalize-left : (ν ∙ (f ◁ id₌ (Cone.left s))) =₂ ν
    normalize-left = comp₌-unitʳ-One ν ∙
      comp₌-cong (id₌ ν) (postWhisker-id₌ f (Cone.left s))

    normalize-right : ((g ◁ id₌ (Cone.right s)) ∙ Cone.match s) =₂ Cone.match s
    normalize-right = comp₌-unitˡ-One (Cone.match s) ∙
      comp₌-cong (postWhisker-id₌ g (Cone.right s)) (id₌ (Cone.match s))
```



## Inverse change and restriction

```agda
  cone-change-right-inverse : {C D E T : CAT Γ} {f : MAP C E} {g g′ : MAP D E}
    (δ : g =₁ g′) (s : Cone f g T)
    → ConeIdentification₁ (cone-change-right (δ ⁻¹) (cone-change-right δ s)) s
  cone-change-right-inverse δ s = cone-retarget-match-identification _ (Cone.match s)
    (comp₌-unitˡ-One (Cone.match s) ∙
      (comp₌-cong (comp₌-inverseˡ-One (δ ▷ Cone.right s)) (id₌ (Cone.match s)) ∙
        ((comp₌-assoc ((δ ▷ Cone.right s) ⁻¹) (δ ▷ Cone.right s) (Cone.match s)) ⁻¹ ∙
          comp₌-cong (preWhisker-inverse δ (Cone.right s))
            (id₌ ((δ ▷ Cone.right s) ∙ Cone.match s)))))

  cone-change-right-restrict : {C D E R T : CAT Γ}
    {f : MAP C E} {g g′ : MAP D E} (δ : g =₁ g′)
    (r : MAP R T) (s : Cone f g T)
    → ConeIdentification₁ (cone-restrict r (cone-change-right δ s))
        (cone-change-right δ (cone-restrict r s))
  cone-change-right-restrict {f = f} {g} {g′} δ r s =
    cone-retarget-match-identification _ _ normalization
    where
    changed-associator = comp-assoc r (Cone.right s) g′
    original-associator = comp-assoc r (Cone.right s) g
    arrow-restricted = (δ ▷ Cone.right s) ▷ r
    match-restricted = Cone.match s ▷ r
    inverse-left-associator = (comp-assoc r (Cone.left s) f) ⁻¹
    tail = match-restricted ∙ inverse-left-associator

    normalization : Cone.match (cone-restrict r (cone-change-right δ s)) =₂
      Cone.match (cone-change-right δ (cone-restrict r s))
    normalization = comp₌-assoc (δ ▷ (Cone.right s ∘ r)) original-associator tail ∙
      (comp₌-cong (preWhisker-comp-One δ (Cone.right s) r) (id₌ tail) ∙
        ((comp₌-assoc changed-associator arrow-restricted tail) ⁻¹ ∙
          comp₌-cong (id₌ changed-associator)
            (comp₌-assoc arrow-restricted match-restricted inverse-left-associator ∙
              comp₌-cong (preWhisker-comp₌ (δ ▷ Cone.right s) (Cone.match s) r)
                (id₌ inverse-left-associator))))
```

## Symmetry

Swapping the legs inverts the specified matching. The action on complete
cone identifications reverses the vertical direction of their square, exchanging its edges and inverting its sides.

```agda
  cone-swap : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    → Cone f g T → Cone g f T
  cone-swap s = record
    { left = Cone.right s; right = Cone.left s; match = (Cone.match s) ⁻¹ }

  cone-swap-identification : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g T} → ConeIdentification₁ s t
    → ConeIdentification₁ (cone-swap s) (cone-swap t)
  cone-swap-identification Φ = record
    { left = ConeIdentification₁.right Φ
    ; right = ConeIdentification₁.left Φ
    ; compatible = inverse-square₌ (ConeIdentification₁.compatible Φ) }

  cone-change-left : {C D E T : CAT Γ} {f f′ : MAP C E} {g : MAP D E}
    → f =₁ f′ → Cone f g T → Cone f′ g T
  cone-change-left δ s = cone-swap (cone-change-right δ (cone-swap s))

  cone-change-left-identification : {C D E T : CAT Γ}
    {f f′ : MAP C E} {g : MAP D E} (δ : f =₁ f′)
    {s t : Cone f g T} → ConeIdentification₁ s t
    → ConeIdentification₁ (cone-change-left δ s) (cone-change-left δ t)
  cone-change-left-identification δ Φ = cone-swap-identification
    (cone-change-right-identification δ (cone-swap-identification Φ))
```



```agda
  cone-swap-twice : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) → ConeIdentification₁ (cone-swap (cone-swap s)) s
  cone-swap-twice s = cone-retarget-match-identification _ (Cone.match s)
    (inverse-inverse (Cone.match s))

  cone-swap-restrict : {C D E R T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (r : MAP R T) (s : Cone f g T)
    → ConeIdentification₁ (cone-restrict r (cone-swap s)) (cone-swap (cone-restrict r s))
  cone-swap-restrict {f = f} {g} r s =
    cone-retarget-match-identification _ _ (normalization ⁻¹)
    where
    left-associator = comp-assoc r (Cone.left s) f
    right-associator = comp-assoc r (Cone.right s) g
    restricted-match = Cone.match s ▷ r

    normalization : Cone.match (cone-swap (cone-restrict r s)) =₂
      Cone.match (cone-restrict r (cone-swap s))
    normalization =
      comp₌-cong (id₌ left-associator)
        (comp₌-cong ((preWhisker-inverse (Cone.match s) r) ⁻¹) (id₌ (right-associator ⁻¹))) ∙
      (comp₌-assoc left-associator (restricted-match ⁻¹) (right-associator ⁻¹) ∙
        (comp₌-cong
          (comp₌-cong (inverse-inverse left-associator) (id₌ (restricted-match ⁻¹)) ∙
            inverse-composite restricted-match (left-associator ⁻¹))
          (id₌ (right-associator ⁻¹)) ∙
          inverse-composite right-associator (restricted-match ∙ left-associator ⁻¹)))
```

## The conventional left-change matching

Left change was constructed through symmetry. Its matching compares to the
original matching followed by the inverse restricted arrow identification.
This computation makes that client boundary available without a new choice.

```agda
  cone-change-left-matching : {C D E T : CAT Γ} {f f′ : MAP C E} {g : MAP D E}
    (δ : f =₁ f′) (s : Cone f g T)
    → Cone.match (cone-change-left δ s) =₂
        (Cone.match s ∙ (δ ▷ Cone.left s) ⁻¹)
  cone-change-left-matching δ s =
    comp₌-cong (inverse-inverse (Cone.match s)) (id₌ ((δ ▷ Cone.left s) ⁻¹)) ∙
      inverse-composite (δ ▷ Cone.left s) ((Cone.match s) ⁻¹)
```

## Changing the legs

Changing both legs transports the matching along their postwhiskered
identifications. The endpoint-change square is the complete cone comparison.
For an already supplied cone comparison, the same square computes the
transported matching.

```agda
  cone-change-legs : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) (p : MAP T C) (q : MAP T D)
    → Cone.left s =₁ p → Cone.right s =₁ q → Cone f g T
  cone-change-legs {f = f} {g} s p q α β = record
    { left = p; right = q
    ; match = changeEndpoints (f ◁ α) (g ◁ β) (Cone.match s) }

  cone-change-legs-β : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) (p : MAP T C) (q : MAP T D)
    (α : Cone.left s =₁ p) (β : Cone.right s =₁ q)
    → ConeIdentification₁ s (cone-change-legs s p q α β)
  cone-change-legs-β {f = f} {g} s p q α β = record
    { left = α; right = β
    ; compatible = transpose-square₌ (changeEndpoints-to-square
        (f ◁ α) (g ◁ β) (Cone.match s) (Cone.match (cone-change-legs s p q α β))
        (id₌ (Cone.match (cone-change-legs s p q α β)))) }

  cone-change-legs-match : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g T} (Φ : ConeIdentification₁ s t)
    → Cone.match (cone-change-legs s (Cone.left t) (Cone.right t)
        (ConeIdentification₁.left Φ) (ConeIdentification₁.right Φ)) =₂ Cone.match t
  cone-change-legs-match {f = f} {g} {s} {t} Φ = square-to-changeEndpoints
    (f ◁ ConeIdentification₁.left Φ) (g ◁ ConeIdentification₁.right Φ)
    (Cone.match s) (Cone.match t) (transpose-square₌ (ConeIdentification₁.compatible Φ))
```

## Left-arrow inverse and restriction laws

Left-arrow change is symmetry, right-arrow change, then symmetry. Its full
inverse and restriction comparisons follow that same construction; they do
not silently replace its matching by the conventional normalized formula.

```agda
  cone-change-right-inverseʳ : {C D E T : CAT Γ} {f : MAP C E} {g g′ : MAP D E}
    (δ : g =₁ g′) (s : Cone f g′ T)
    → ConeIdentification₁ (cone-change-right δ (cone-change-right (δ ⁻¹) s)) s
  cone-change-right-inverseʳ δ s = cone-retarget-match-identification _ (Cone.match s)
    (comp₌-unitˡ-One (Cone.match s) ∙
      (comp₌-cong (comp₌-inverseʳ-One (δ ▷ Cone.right s)) (id₌ (Cone.match s)) ∙
        ((comp₌-assoc (δ ▷ Cone.right s) ((δ ▷ Cone.right s) ⁻¹) (Cone.match s)) ⁻¹ ∙
          comp₌-cong (id₌ (δ ▷ Cone.right s))
            (comp₌-cong (preWhisker-inverse δ (Cone.right s)) (id₌ (Cone.match s))))))

  cone-change-left-inverse : {C D E T : CAT Γ} {f f′ : MAP C E} {g : MAP D E}
    (δ : f =₁ f′) (s : Cone f g T)
    → ConeIdentification₁ (cone-change-left (δ ⁻¹) (cone-change-left δ s)) s
  cone-change-left-inverse δ s = cone-compose (cone-swap-twice s)
    (cone-compose (cone-swap-identification (cone-change-right-inverse δ (cone-swap s)))
      (cone-swap-identification (cone-change-right-identification (δ ⁻¹)
        (cone-swap-twice (cone-change-right δ (cone-swap s))))))

  cone-change-left-inverseʳ : {C D E T : CAT Γ} {f f′ : MAP C E} {g : MAP D E}
    (δ : f =₁ f′) (s : Cone f′ g T)
    → ConeIdentification₁ (cone-change-left δ (cone-change-left (δ ⁻¹) s)) s
  cone-change-left-inverseʳ δ s = cone-compose (cone-swap-twice s)
    (cone-compose (cone-swap-identification (cone-change-right-inverseʳ δ (cone-swap s)))
      (cone-swap-identification (cone-change-right-identification δ
        (cone-swap-twice (cone-change-right (δ ⁻¹) (cone-swap s))))))

  cone-change-left-restrict : {C D E R T : CAT Γ}
    {f f′ : MAP C E} {g : MAP D E} (δ : f =₁ f′)
    (r : MAP R T) (s : Cone f g T)
    → ConeIdentification₁ (cone-restrict r (cone-change-left δ s))
        (cone-change-left δ (cone-restrict r s))
  cone-change-left-restrict δ r s = cone-compose
    (cone-swap-identification (cone-change-right-identification δ (cone-swap-restrict r s)))
    (cone-compose (cone-swap-identification (cone-change-right-restrict δ r (cone-swap s)))
      (cone-swap-restrict r (cone-change-right δ (cone-swap s))))
```
