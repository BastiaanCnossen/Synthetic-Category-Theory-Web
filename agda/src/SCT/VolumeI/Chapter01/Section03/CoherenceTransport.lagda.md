# Transporting a finite coherence diagram

The internal-coherence argument fixes comparisons at the vertices of its
diagram. Transporting an edge means composing with the target comparison
and the inverse source comparison. This file proves the cancellation used
when transported edges are composed. It depends only on Section 1.1 and
does not assume any mapping-composition coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter01.Section03.CoherenceTransport
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv)

changeEndpoints : {C D : CAT} {f f′ g g′ : MAP C D}
  → NatIso f f′ → NatIso g g′ → NatIso f g → NatIso f′ g′
changeEndpoints p q α = q ∙ (α ∙ invIso p)

changeEndpoints-cong : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) {α β : NatIso f g}
  → Iso₂ α β → Iso₂ (changeEndpoints p q α) (changeEndpoints p q β)
changeEndpoints-cong p q comparison =
  isoComp-cong (idIso q) (isoComp-cong comparison (idIso (invIso p)))

private
  cancel-inverse-pair : {C D : CAT} {f g g′ : MAP C D}
    (q : NatIso g g′) (u : NatIso f g)
    → Iso₂ (invIso q ∙ (q ∙ u)) u
  cancel-inverse-pair q u = isoComp-unitˡ-at u ∙
    (isoComp-cong (isoComp-inverseˡ-at q) (idIso u) ∙
      invIso (isoComp-assoc-at (invIso q) q u))

changeEndpoints-comp : {C D : CAT} {f f′ g g′ h h′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) (r : NatIso h h′)
  (β : NatIso g h) (α : NatIso f g)
  → Iso₂ (changeEndpoints q r β ∙ changeEndpoints p q α)
      (changeEndpoints p r (β ∙ α))
changeEndpoints-comp p q r β α =
  let remaining = α ∙ invIso p
      cancel : Iso₂ ((β ∙ invIso q) ∙ (q ∙ remaining)) (β ∙ remaining)
      cancel = isoComp-cong (idIso β) (cancel-inverse-pair q remaining) ∙
        isoComp-assoc-at β (invIso q) (q ∙ remaining)
      regroup : Iso₂ (β ∙ remaining) ((β ∙ α) ∙ invIso p)
      regroup = invIso (isoComp-assoc-at β α (invIso p))
  in isoComp-cong (idIso r) (regroup ∙ cancel) ∙
    isoComp-assoc-at r (β ∙ invIso q) (q ∙ remaining)

changeEndpoints-id : {C D : CAT} {f g : MAP C D} (p : NatIso f g)
  → Iso₂ (changeEndpoints p p (idIso f)) (idIso g)
changeEndpoints-id p = isoComp-inverseʳ-at p ∙
  isoComp-cong (idIso p) (isoComp-unitˡ-at (invIso p))
```

Changing endpoints is also an actual equivalence of isomorphism animae.
Its reflection clause cancels the common outside comparisons of two
transported paths, retaining a witness on the entire isomorphism anima.

```agda
changeEndpoints-map : {C D : CAT} {f f′ g g′ : MAP C D}
  → NatIso f f′ → NatIso g g′ → MAP (f ≅ g) (f′ ≅ g′)
changeEndpoints-map p q = leftMultiply q ∘ rightMultiply (invIso p)

changeEndpoints-map-isEquiv : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) → IsEquiv (changeEndpoints-map p q)
changeEndpoints-map-isEquiv p q = equiv-compose
  (rightMultiply (invIso p)) (leftMultiply q)
  (rightMultiply-isEquiv (invIso p)) (leftMultiply-isEquiv q)

changeEndpoints-at : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) (α : NatIso f g)
  → Iso₂ (changeEndpoints-map p q ∘ α) (changeEndpoints p q α)
changeEndpoints-at p q α = isoComp-evaluate (const q) (id _)
  (rightMultiply (invIso p) ∘ α)
  (const-evaluate q (rightMultiply (invIso p) ∘ α))
  (isoComp-evaluate (id _) (const (invIso p)) α
    (comp-unitˡ α) (const-evaluate (invIso p) α) ∙
      comp-unitˡ (rightMultiply (invIso p) ∘ α)) ∙
  comp-assoc α (rightMultiply (invIso p)) (leftMultiply q)

changeEndpoints-reflect : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) (α β : NatIso f g)
  → Iso₂ (changeEndpoints p q α) (changeEndpoints p q β) → Iso₂ α β
changeEndpoints-reflect p q α β comparison =
  equiv-reflect (changeEndpoints-map-isEquiv p q) α β
    (invIso (changeEndpoints-at p q β) ∙ (comparison ∙ changeEndpoints-at p q α))
```

A commuting square can equivalently be read as an identification with the
transported edge. This is useful when naturality supplies the square, while
the final diagram argument needs a common expression for each edge.

```agda
square-to-changeEndpoints : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) (α : NatIso f g) (β : NatIso f′ g′)
  → Iso₂ (q ∙ α) (β ∙ p) → Iso₂ (changeEndpoints p q α) β
square-to-changeEndpoints p q α β square = isoComp-unitʳ-at β ∙
  (isoComp-cong (idIso β) (isoComp-inverseʳ-at p) ∙
  (isoComp-assoc-at β p (invIso p) ∙
  (isoComp-cong square (idIso (invIso p)) ∙
    invIso (isoComp-assoc-at q α (invIso p)))))

changeEndpoints-to-square : {C D : CAT} {f f′ g g′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) (α : NatIso f g) (β : NatIso f′ g′)
  → Iso₂ (changeEndpoints p q α) β → Iso₂ (q ∙ α) (β ∙ p)
changeEndpoints-to-square p q α β comparison =
  isoComp-cong comparison (idIso p) ∙
  (invIso (isoComp-assoc-at q (α ∙ invIso p) p) ∙
    isoComp-cong (idIso q)
      (invIso (isoComp-assoc-at α (invIso p) p) ∙
        (isoComp-cong (idIso α) (invIso (isoComp-inverseˡ-at p)) ∙
          invIso (isoComp-unitʳ-at α))))
```

Consequently a two-edge route and a three-edge route inherit an existing
identification when the same vertex comparisons are used on both routes.
This is only the telescoping step of a pentagon argument. The separate
comparison of each evaluated edge with its transported primitive edge is
still required when applying it to internal composition.

```agda
changeEndpoints-comp₃ : {C D : CAT} {f f′ g g′ h h′ k k′ : MAP C D}
  (p : NatIso f f′) (q : NatIso g g′) (r : NatIso h h′) (s : NatIso k k′)
  (γ : NatIso h k) (β : NatIso g h) (α : NatIso f g)
  → Iso₂ ((changeEndpoints r s γ ∙ changeEndpoints q r β) ∙ changeEndpoints p q α)
      (changeEndpoints p s ((γ ∙ β) ∙ α))
changeEndpoints-comp₃ p q r s γ β α = changeEndpoints-comp p q s (γ ∙ β) α ∙
  isoComp-cong (changeEndpoints-comp q r s γ β) (idIso (changeEndpoints p q α))

transport-pentagon : {C D : CAT} {v₀ v₁ v₂ v₃ v₄ w₀ w₁ w₂ w₃ w₄ : MAP C D}
  (p₀ : NatIso v₀ w₀) (p₁ : NatIso v₁ w₁) (p₂ : NatIso v₂ w₂)
  (p₃ : NatIso v₃ w₃) (p₄ : NatIso v₄ w₄)
  (α : NatIso v₀ v₁) (β : NatIso v₁ v₄)
  (γ : NatIso v₀ v₂) (δ : NatIso v₂ v₃) (ε : NatIso v₃ v₄)
  → Iso₂ (β ∙ α) ((ε ∙ δ) ∙ γ)
  → Iso₂ (changeEndpoints p₁ p₄ β ∙ changeEndpoints p₀ p₁ α)
      ((changeEndpoints p₃ p₄ ε ∙ changeEndpoints p₂ p₃ δ) ∙ changeEndpoints p₀ p₂ γ)
transport-pentagon p₀ p₁ p₂ p₃ p₄ α β γ δ ε pentagon =
  invIso (changeEndpoints-comp₃ p₀ p₂ p₃ p₄ ε δ γ) ∙
    (changeEndpoints-cong p₀ p₄ pentagon ∙ changeEndpoints-comp p₀ p₁ p₄ β α)

transport-triangle : {C D : CAT} {v₀ v₁ v₂ w₀ w₁ w₂ : MAP C D}
  (p₀ : NatIso v₀ w₀) (p₁ : NatIso v₁ w₁) (p₂ : NatIso v₂ w₂)
  (α : NatIso v₀ v₂) (β : NatIso v₀ v₁) (γ : NatIso v₁ v₂)
  → Iso₂ α (γ ∙ β)
  → Iso₂ (changeEndpoints p₀ p₂ α)
      (changeEndpoints p₁ p₂ γ ∙ changeEndpoints p₀ p₁ β)
transport-triangle p₀ p₁ p₂ α β γ triangle =
  invIso (changeEndpoints-comp p₀ p₁ p₂ γ β) ∙ changeEndpoints-cong p₀ p₂ triangle
```

One useful rearrangement of a pentagon isolates its left corner. This
lemma is a consequence of the supplied identity, using only cancellation.

```agda
pentagon-left-corner : {C D : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP C D}
  (A : NatIso x₁ x₄) (B : NatIso x₀ x₁) (C′ : NatIso x₃ x₄)
  (D′ : NatIso x₂ x₃) (E : NatIso x₀ x₂)
  → Iso₂ (A ∙ B) (C′ ∙ (D′ ∙ E))
  → Iso₂ (invIso D′ ∙ (invIso C′ ∙ A)) (E ∙ invIso B)
pentagon-left-corner A B C′ D′ E pentagon =
  let clear : Iso₂ ((A ∙ B) ∙ invIso B) A
      clear = isoComp-unitʳ-at A ∙
        (isoComp-cong (idIso A) (isoComp-inverseʳ-at B) ∙ isoComp-assoc-at A B (invIso B))
      expandCorner : Iso₂ A (C′ ∙ (D′ ∙ (E ∙ invIso B)))
      expandCorner = isoComp-cong (idIso C′) (isoComp-assoc-at D′ E (invIso B)) ∙
        (isoComp-assoc-at C′ (D′ ∙ E) (invIso B) ∙
          (isoComp-cong pentagon (idIso (invIso B)) ∙ invIso clear))
  in cancel-inverse-pair D′ (E ∙ invIso B) ∙
    (isoComp-cong (idIso (invIso D′)) (cancel-inverse-pair C′ (D′ ∙ (E ∙ invIso B))) ∙
      isoComp-cong (idIso (invIso D′)) (isoComp-cong (idIso (invIso C′)) expandCorner))
```
