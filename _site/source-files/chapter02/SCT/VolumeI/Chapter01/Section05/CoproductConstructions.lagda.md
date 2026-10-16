# Coproduct constructions

The chosen copair induces coproduct maps, swap, units and reassociation.
Their comparisons are derived from the chosen beta, eta and action laws.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section05.CoproductConstructions where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section05.Coproducts
open import SCT.VolumeI.Chapter01.Section05.Copairing
open import SCT.VolumeI.Chapter01.Section05.Initial using (Zero; initiate; initial-unique)
```

## Induced functors

The coproduct of f and g is the copair of their composites with the target
inclusions. Its congruence acts on arbitrary identification families.
Identity and composition have their specified comparison components.

```agda
module _ {Γ : Context} where
  coproductMap : {C C′ D D′ : CAT Γ}
    → MAP C C′ → MAP D D′ → MAP (C ⊔ D) (C′ ⊔ D′)
  coproductMap f g = copair (in₁ ∘ f) (in₂ ∘ g)

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    coproductMap-cong : {C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
      → f ＝ f′ → g ＝ g′ → coproductMap f g ＝ coproductMap f′ g′
    coproductMap-cong α β = copair-cong (in₁ ◁ α) (in₂ ◁ β)

  coproductMap-id : (C D : CAT Γ)
    → coproductMap (id C) (id D) =₁ id (C ⊔ D)
  coproductMap-id C D = copair-inclusions C D ∙
    copair-cong (comp-unitʳ in₁) (comp-unitʳ in₂)

  coproductMap-comp : {C C′ C″ D D′ D″ : CAT Γ}
    (f : MAP C C′) (f′ : MAP C′ C″) (g : MAP D D′) (g′ : MAP D′ D″)
    → (coproductMap f′ g′ ∘ coproductMap f g) =₁ coproductMap (f′ ∘ f) (g′ ∘ g)
  coproductMap-comp f f′ g g′ =
    copair-cong (comp-assoc f f′ in₁ ∙ copair-pre₁ (in₁ ∘ f′) (in₂ ∘ g′) f)
      (comp-assoc g g′ in₂ ∙ copair-pre₂ (in₁ ∘ f′) (in₂ ∘ g′) g) ∙
    copair-post (in₁ ∘ f) (in₂ ∘ g) (coproductMap f′ g′)

  coproductMap-isEquiv : {C C′ D D′ : CAT Γ} (f : MAP C C′) (g : MAP D D′)
    → IsEquiv f → IsEquiv g → IsEquiv (coproductMap f g)
  coproductMap-isEquiv {C} {C′} {D} {D′} f g ef eg = record
    { inverse = coproductMap (IsEquiv.inverse ef) (IsEquiv.inverse eg)
    ; left-inverse-law = (coproductMap-comp f (IsEquiv.inverse ef) g (IsEquiv.inverse eg)) ⁻¹ ∙
        (coproductMap-cong (IsEquiv.left-inverse-law ef) (IsEquiv.left-inverse-law eg) ∙
          (coproductMap-id C D) ⁻¹)
    ; right-inverse-law = (coproductMap-comp (IsEquiv.inverse ef) f (IsEquiv.inverse eg) g) ⁻¹ ∙
        (coproductMap-cong (IsEquiv.right-inverse-law ef) (IsEquiv.right-inverse-law eg) ∙
          (coproductMap-id C′ D′) ⁻¹) }
```

## Symmetry

Swap is the copair of the reversed inclusions. Its inverse is the opposite
swap, since their composite restricts to the two original inclusions.

```agda
  coproductSwap : {C D : CAT Γ} → MAP (C ⊔ D) (D ⊔ C)
  coproductSwap = copair in₂ in₁

  coproductSwap-swap : (C D : CAT Γ)
    → (coproductSwap {C = D} {D = C} ∘ coproductSwap {C = C} {D = D}) =₁ id (C ⊔ D)
  coproductSwap-swap C D = copair-inclusions C D ∙
    (copair-cong (copair-β₂ in₂ in₁) (copair-β₁ in₂ in₁) ∙ copair-post in₂ in₁ coproductSwap)

  coproductSwap-isEquiv : (C D : CAT Γ) → IsEquiv (coproductSwap {C = C} {D = D})
  coproductSwap-isEquiv C D = record
    { inverse = coproductSwap
    ; left-inverse-law = (coproductSwap-swap C D) ⁻¹
    ; right-inverse-law = (coproductSwap-swap D C) ⁻¹ }
```

## Units

Copairing initiation and the identity gives the two unit functors. The
relevant inclusion is the inverse. To compute the inverse composite,
postcompose the chosen copair with that inclusion, compare its two inputs
with the original inclusions, and use copair-inclusions. Initiality supplies
the comparison at Zero; strictness is not used.

```agda
  coproduct-unitˡ : (C : CAT Γ) → MAP (Zero ⊔ C) C
  coproduct-unitˡ C = copair (initiate C) (id C)

  coproduct-unitˡ-isEquiv : (C : CAT Γ) → IsEquiv (coproduct-unitˡ C)
  coproduct-unitˡ-isEquiv C = record
    { inverse = in₂
    ; left-inverse-law = (copair-inclusions Zero C ∙
        (copair-cong (initial-unique _ _) (comp-unitʳ in₂) ∙
          copair-post (initiate C) (id C) in₂)) ⁻¹
    ; right-inverse-law = (copair-β₂ (initiate C) (id C)) ⁻¹ }

  coproduct-unitʳ : (C : CAT Γ) → MAP (C ⊔ Zero) C
  coproduct-unitʳ C = copair (id C) (initiate C)

  coproduct-unitʳ-isEquiv : (C : CAT Γ) → IsEquiv (coproduct-unitʳ C)
  coproduct-unitʳ-isEquiv C = record
    { inverse = in₁
    ; left-inverse-law = (copair-inclusions C Zero ∙
        (copair-cong (comp-unitʳ in₁) (initial-unique _ _) ∙
          copair-post (id C) (initiate C) in₁)) ⁻¹
    ; right-inverse-law = (copair-β₁ (id C) (initiate C)) ⁻¹ }
```

## Reassociation

The two parenthesizations are displayed as Source and Target. The forward
and backward functors are nested copairs. Their composites restrict to the
three inclusions by the selected beta comparisons, and eta finishes the
inverse laws. This proves a reassociation equivalence; no coproduct pentagon
is asserted.

```agda
  module CoproductAssociativity (C D E : CAT Γ) where
    Source : CAT Γ
    Source = (C ⊔ D) ⊔ E

    Target : CAT Γ
    Target = C ⊔ (D ⊔ E)

    private
      forward-left : MAP (C ⊔ D) Target
      forward-left = copair in₁ (in₂ ∘ in₁)

      backward-right : MAP (D ⊔ E) Source
      backward-right = copair (in₁ ∘ in₂) in₂

    forward : MAP Source Target
    forward = copair forward-left (in₂ ∘ in₂)

    backward : MAP Target Source
    backward = copair (in₁ ∘ in₁) backward-right

    private
      backward-forward-left : (backward ∘ forward-left) =₁ in₁
      backward-forward-left = copair-η in₁ ∙
        (copair-cong (copair-β₁ (in₁ ∘ in₁) backward-right)
          (copair-β₁ (in₁ ∘ in₂) in₂ ∙ copair-pre₂ (in₁ ∘ in₁) backward-right in₁) ∙
          copair-post in₁ (in₂ ∘ in₁) backward)

      backward-forward-right : (backward ∘ (in₂ ∘ in₂)) =₁ in₂
      backward-forward-right = copair-β₂ (in₁ ∘ in₂) in₂ ∙
        copair-pre₂ (in₁ ∘ in₁) backward-right in₂

    backward-forward : (backward ∘ forward) =₁ id Source
    backward-forward = copair-inclusions (C ⊔ D) E ∙
      (copair-cong backward-forward-left backward-forward-right ∙
        copair-post forward-left (in₂ ∘ in₂) backward)

    private
      forward-backward-left : (forward ∘ (in₁ ∘ in₁)) =₁ in₁
      forward-backward-left = copair-β₁ in₁ (in₂ ∘ in₁) ∙
        copair-pre₁ forward-left (in₂ ∘ in₂) in₁

      forward-backward-right : (forward ∘ backward-right) =₁ in₂
      forward-backward-right = copair-η in₂ ∙
        (copair-cong
          (copair-β₂ in₁ (in₂ ∘ in₁) ∙ copair-pre₁ forward-left (in₂ ∘ in₂) in₂)
          (copair-β₂ forward-left (in₂ ∘ in₂)) ∙
          copair-post (in₁ ∘ in₂) in₂ forward)

    forward-backward : (forward ∘ backward) =₁ id Target
    forward-backward = copair-inclusions C (D ⊔ E) ∙
      (copair-cong forward-backward-left forward-backward-right ∙
        copair-post (in₁ ∘ in₁) backward-right forward)

    forward-isEquiv : IsEquiv forward
    forward-isEquiv = record
      { inverse = backward
      ; left-inverse-law = backward-forward ⁻¹
      ; right-inverse-law = forward-backward ⁻¹ }
```
