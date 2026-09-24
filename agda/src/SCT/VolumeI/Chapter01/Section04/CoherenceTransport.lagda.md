# Transporting a finite coherence diagram

The internal-coherence argument fixes comparisons at the vertices of its
diagram. Transporting an edge means composing with the target comparison
and the inverse source comparison. This file proves the cancellation used
when transported edges are composed. It depends only on Section 1.1 and
does not assume any mapping-composition coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter01.Section04.CoherenceTransport
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv)

changeEndpoints : {C D : CAT} {f f′ g g′ : MAP C D}
  → f =₁ f′ → g =₁ g′ → f =₁ g → f′ =₁ g′
changeEndpoints p q α = q ∙ (α ∙ p ⁻¹)

changeEndpoints-cong : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) {α β : f =₁ g}
  → α =₂ β → (changeEndpoints p q α) =₂ (changeEndpoints p q β)
changeEndpoints-cong p q comparison =
  isoComp-cong (idIso q) (isoComp-cong comparison (idIso (p ⁻¹)))

private
  cancel-inverse-pair : {C D : CAT} {f g g′ : MAP C D}
    (q : g =₁ g′) (u : f =₁ g)
    → (q ⁻¹ ∙ (q ∙ u)) =₂ u
  cancel-inverse-pair q u = isoComp-unitˡ-at u ∙
    (isoComp-cong (isoComp-inverseˡ-at q) (idIso u) ∙
      (isoComp-assoc-at (q ⁻¹) q u) ⁻¹)

changeEndpoints-comp : {C D : CAT} {f f′ g g′ h h′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (r : h =₁ h′)
  (β : g =₁ h) (α : f =₁ g)
  → (changeEndpoints q r β ∙ changeEndpoints p q α) =₂
      (changeEndpoints p r (β ∙ α))
changeEndpoints-comp p q r β α =
  let remaining = α ∙ p ⁻¹
      cancel : ((β ∙ q ⁻¹) ∙ (q ∙ remaining)) =₂ (β ∙ remaining)
      cancel = isoComp-cong (idIso β) (cancel-inverse-pair q remaining) ∙
        isoComp-assoc-at β (q ⁻¹) (q ∙ remaining)
      regroup : (β ∙ remaining) =₂ ((β ∙ α) ∙ p ⁻¹)
      regroup = (isoComp-assoc-at β α (p ⁻¹)) ⁻¹
  in isoComp-cong (idIso r) (regroup ∙ cancel) ∙
    isoComp-assoc-at r (β ∙ q ⁻¹) (q ∙ remaining)

changeEndpoints-id : {C D : CAT} {f g : MAP C D} (p : f =₁ g)
  → (changeEndpoints p p (idIso f)) =₂ (idIso g)
changeEndpoints-id p = isoComp-inverseʳ-at p ∙
  isoComp-cong (idIso p) (isoComp-unitˡ-at (p ⁻¹))
```

Changing endpoints is also an actual equivalence of isomorphism animae.
Its reflection clause cancels the common outside comparisons of two
transported paths, retaining a witness on the entire isomorphism anima.

```agda
changeEndpoints-map : {C D : CAT} {f f′ g g′ : MAP C D}
  → f =₁ f′ → g =₁ g′ → MAP (f ＝ g) (f′ ＝ g′)
changeEndpoints-map p q = leftMultiply q ∘ rightMultiply (p ⁻¹)

changeEndpoints-map-isEquiv : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) → IsEquiv (changeEndpoints-map p q)
changeEndpoints-map-isEquiv p q = equiv-compose
  (rightMultiply (p ⁻¹)) (leftMultiply q)
  (rightMultiply-isEquiv (p ⁻¹)) (leftMultiply-isEquiv q)

changeEndpoints-at : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (α : f =₁ g)
  → (changeEndpoints-map p q ∘ α) =₂ (changeEndpoints p q α)
changeEndpoints-at p q α = isoComp-evaluate (const q) (id _)
  (rightMultiply (p ⁻¹) ∘ α)
  (const-evaluate q (rightMultiply (p ⁻¹) ∘ α))
  (isoComp-evaluate (id _) (const (p ⁻¹)) α
    (comp-unitˡ α) (const-evaluate (p ⁻¹) α) ∙
      comp-unitˡ (rightMultiply (p ⁻¹) ∘ α)) ∙
  comp-assoc α (rightMultiply (p ⁻¹)) (leftMultiply q)

changeEndpoints-reflect : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (α β : f =₁ g)
  → (changeEndpoints p q α) =₂ (changeEndpoints p q β) → α =₂ β
changeEndpoints-reflect p q α β comparison =
  equiv-reflect (changeEndpoints-map-isEquiv p q) α β
    ((changeEndpoints-at p q β) ⁻¹ ∙ (comparison ∙ changeEndpoints-at p q α))
```

A commuting square can equivalently be read as an identification with the
transported edge. This is useful when naturality supplies the square, while
the final diagram argument needs a common expression for each edge.

```agda
square-to-changeEndpoints : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (α : f =₁ g) (β : f′ =₁ g′)
  → (q ∙ α) =₂ (β ∙ p) → (changeEndpoints p q α) =₂ β
square-to-changeEndpoints p q α β square = isoComp-unitʳ-at β ∙
  (isoComp-cong (idIso β) (isoComp-inverseʳ-at p) ∙
  (isoComp-assoc-at β p (p ⁻¹) ∙
  (isoComp-cong square (idIso (p ⁻¹)) ∙
    (isoComp-assoc-at q α (p ⁻¹)) ⁻¹)))

changeEndpoints-to-square : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (α : f =₁ g) (β : f′ =₁ g′)
  → (changeEndpoints p q α) =₂ β → (q ∙ α) =₂ (β ∙ p)
changeEndpoints-to-square p q α β comparison =
  isoComp-cong comparison (idIso p) ∙
  ((isoComp-assoc-at q (α ∙ p ⁻¹) p) ⁻¹ ∙
    isoComp-cong (idIso q)
      ((isoComp-assoc-at α (p ⁻¹) p) ⁻¹ ∙
        (isoComp-cong (idIso α) ((isoComp-inverseˡ-at p) ⁻¹) ∙
          (isoComp-unitʳ-at α) ⁻¹)))
```

Consequently a two-edge route and a three-edge route inherit an existing
identification when the same vertex comparisons are used on both routes.
This is only the telescoping step of a pentagon argument. The separate
comparison of each evaluated edge with its transported primitive edge is
still required when applying it to internal composition.

```agda
changeEndpoints-comp₃ : {C D : CAT} {f f′ g g′ h h′ k k′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (r : h =₁ h′) (s : k =₁ k′)
  (γ : h =₁ k) (β : g =₁ h) (α : f =₁ g)
  → ((changeEndpoints r s γ ∙ changeEndpoints q r β) ∙ changeEndpoints p q α) =₂
      (changeEndpoints p s ((γ ∙ β) ∙ α))
changeEndpoints-comp₃ p q r s γ β α = changeEndpoints-comp p q s (γ ∙ β) α ∙
  isoComp-cong (changeEndpoints-comp q r s γ β) (idIso (changeEndpoints p q α))

transport-pentagon : {C D : CAT} {v₀ v₁ v₂ v₃ v₄ w₀ w₁ w₂ w₃ w₄ : MAP C D}
  (p₀ : v₀ =₁ w₀) (p₁ : v₁ =₁ w₁) (p₂ : v₂ =₁ w₂)
  (p₃ : v₃ =₁ w₃) (p₄ : v₄ =₁ w₄)
  (α : v₀ =₁ v₁) (β : v₁ =₁ v₄)
  (γ : v₀ =₁ v₂) (δ : v₂ =₁ v₃) (ε : v₃ =₁ v₄)
  → (β ∙ α) =₂ ((ε ∙ δ) ∙ γ)
  → (changeEndpoints p₁ p₄ β ∙ changeEndpoints p₀ p₁ α) =₂
      ((changeEndpoints p₃ p₄ ε ∙ changeEndpoints p₂ p₃ δ) ∙ changeEndpoints p₀ p₂ γ)
transport-pentagon p₀ p₁ p₂ p₃ p₄ α β γ δ ε pentagon =
  (changeEndpoints-comp₃ p₀ p₂ p₃ p₄ ε δ γ) ⁻¹ ∙
    (changeEndpoints-cong p₀ p₄ pentagon ∙ changeEndpoints-comp p₀ p₁ p₄ β α)

transport-triangle : {C D : CAT} {v₀ v₁ v₂ w₀ w₁ w₂ : MAP C D}
  (p₀ : v₀ =₁ w₀) (p₁ : v₁ =₁ w₁) (p₂ : v₂ =₁ w₂)
  (α : v₀ =₁ v₂) (β : v₀ =₁ v₁) (γ : v₁ =₁ v₂)
  → α =₂ (γ ∙ β)
  → (changeEndpoints p₀ p₂ α) =₂
      (changeEndpoints p₁ p₂ γ ∙ changeEndpoints p₀ p₁ β)
transport-triangle p₀ p₁ p₂ α β γ triangle =
  (changeEndpoints-comp p₀ p₁ p₂ γ β) ⁻¹ ∙ changeEndpoints-cong p₀ p₂ triangle
```

One useful rearrangement of a pentagon isolates its left corner. This
lemma is a consequence of the supplied identity, using only cancellation.

```agda
pentagon-left-corner : {C D : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP C D}
  (A : x₁ =₁ x₄) (B : x₀ =₁ x₁) (C′ : x₃ =₁ x₄)
  (D′ : x₂ =₁ x₃) (E : x₀ =₁ x₂)
  → (A ∙ B) =₂ (C′ ∙ (D′ ∙ E))
  → (D′ ⁻¹ ∙ (C′ ⁻¹ ∙ A)) =₂ (E ∙ B ⁻¹)
pentagon-left-corner A B C′ D′ E pentagon =
  let clear : ((A ∙ B) ∙ B ⁻¹) =₂ A
      clear = isoComp-unitʳ-at A ∙
        (isoComp-cong (idIso A) (isoComp-inverseʳ-at B) ∙ isoComp-assoc-at A B (B ⁻¹))
      expandCorner : A =₂ (C′ ∙ (D′ ∙ (E ∙ B ⁻¹)))
      expandCorner = isoComp-cong (idIso C′) (isoComp-assoc-at D′ E (B ⁻¹)) ∙
        (isoComp-assoc-at C′ (D′ ∙ E) (B ⁻¹) ∙
          (isoComp-cong pentagon (idIso (B ⁻¹)) ∙ clear ⁻¹))
  in cancel-inverse-pair D′ (E ∙ B ⁻¹) ∙
    (isoComp-cong (idIso (D′ ⁻¹)) (cancel-inverse-pair C′ (D′ ∙ (E ∙ B ⁻¹))) ∙
      isoComp-cong (idIso (D′ ⁻¹)) (isoComp-cong (idIso (C′ ⁻¹)) expandCorner))
```
