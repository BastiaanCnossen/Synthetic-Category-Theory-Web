# Specializing functors between mapping animae

A functor between mapping animae acts on external functors by naming, applying
that functor, and decoding. Its identification actions are the actual composites
of the naming, whiskering and decoding functors. Recovery uses their chosen
inverse and retains its image equation. Identification families have an
independent arbitrary parameter.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.MappingSpecialization where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-compose; equiv-reflect)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (postWhisker-isEquiv; factor-through-postWhisker)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Points

module _ {Γ : Context} where
  specialize-map : {A B C D : CAT Γ} → MAP (Map A B) (Map C D) → MAP A B → MAP C D
  specialize-map H f = decode (H ∘ name f)

  specialize-map-id : {A B : CAT Γ} (f : MAP A B)
    → specialize-map (id (Map A B)) f =₁ f
  specialize-map-id f = decode-name f ∙ decode⁼ (comp-unitˡ (name f))

  specialize-map-comp : {A B C D E F : CAT Γ}
    (H : MAP (Map A B) (Map C D)) (K : MAP (Map C D) (Map E F)) (f : MAP A B)
    → specialize-map (K ∘ H) f =₁ specialize-map K (specialize-map H f)
  specialize-map-comp H K f = decode⁼
    ((K ◁ name-decode (H ∘ name f)) ⁻¹ ∙ comp-assoc (name f) H K)

  specialize⁼-functor : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
    (f g : MAP A B) → MAP (Equal f g) (Equal (specialize-map H f) (specialize-map H g))
  specialize⁼-functor H f g = decode⁼-functor (H ∘ name f) (H ∘ name g) ∘
    (postWhisker H ∘ name⁼-functor f g)

  specialize-change⁼-functor : {A B C D : CAT Γ}
    (H K : MAP (Map A B) (Map C D)) (f : MAP A B)
    → MAP (Equal H K) (Equal (specialize-map H f) (specialize-map K f))
  specialize-change⁼-functor H K f =
    decode⁼-functor (H ∘ name f) (K ∘ name f) ∘ preWhisker (name f)

  specialize⁼-isEquiv : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
    → IsEquiv H → (f g : MAP A B) → IsEquiv (specialize⁼-functor H f g)
  specialize⁼-isEquiv H e f g =
    equiv-compose (postWhisker H ∘ name⁼-functor f g)
      (decode⁼-functor (H ∘ name f) (H ∘ name g))
      (equiv-compose (name⁼-functor f g) (postWhisker H)
        (name⁼-isEquiv f g) (postWhisker-isEquiv H e (name f) (name g)))
      (decode⁼-isEquiv (H ∘ name f) (H ∘ name g))

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    specialize⁼ : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
      {f g : MAP A B} → f ＝ g → specialize-map H f ＝ specialize-map H g
    specialize⁼ H {f} {g} α = specialize⁼-functor H f g ∘ α

    specialize⁼-cong : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
      {f g : MAP A B} {α β : f ＝ g}
      → α =₁ β → specialize⁼ H α =₁ specialize⁼ H β
    specialize⁼-cong H {f} {g} p = specialize⁼-functor H f g ◁ p

    specialize-change⁼ : {A B C D : CAT Γ} {H K : MAP (Map A B) (Map C D)}
      → H ＝ K → (f : MAP A B) → specialize-map H f ＝ specialize-map K f
    specialize-change⁼ {H = H} {K} τ f = specialize-change⁼-functor H K f ∘ τ

    specialization-reflection : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
      → IsEquiv H → (f g : MAP A B) → (α : specialize-map H f ＝ specialize-map H g)
      → Fact.Factorization (specialize⁼-functor H f g) α
    specialization-reflection H e f g = Fact.factor-through-equiv (specialize⁼-isEquiv H e f g)

    specialize-reflect : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
      → IsEquiv H → (f g : MAP A B) → specialize-map H f ＝ specialize-map H g → f ＝ g
    specialize-reflect H e f g α = Fact.factor (specialization-reflection H e f g α)

    specialize-reflect-β : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
      (e : IsEquiv H) (f g : MAP A B) (α : specialize-map H f ＝ specialize-map H g)
      → specialize⁼ H (specialize-reflect H e f g α) =₁ α
    specialize-reflect-β H e f g α = Fact.triangle (specialization-reflection H e f g α)

    specialize-reflect₂ : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
      → IsEquiv H → {f g : MAP A B} → (α β : f ＝ g)
      → specialize⁼ H α =₁ specialize⁼ H β → α =₁ β
    specialize-reflect₂ H e {f} {g} α β =
      equiv-reflect (specialize⁼-isEquiv H e f g) α β

    factor-through-specialize⁼ : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
      (e : IsEquiv H) {f g : MAP A B} (α β : f ＝ g)
      (p : specialize⁼ H α =₁ specialize⁼ H β)
      → Fact.Factorization (postWhisker (specialize⁼-functor H f g)) p
    factor-through-specialize⁼ H e {f} {g} α β p =
      factor-through-postWhisker (specialize⁼-functor H f g) (specialize⁼-isEquiv H e f g) p
```

## Factoring an external functor

The named functor factors through the supplied equivalence of mapping animae.
Decoding this factor gives an external functor with its specified triangle.

```agda
  record SpecializationFactorization {A B C D : CAT Γ}
    (H : MAP (Map A B) (Map C D)) (g : MAP C D) : Set m where
    field
      factor : MAP A B
      triangle : specialize-map H factor =₁ g

  factor-through-specialize-map : {A B C D : CAT Γ} (H : MAP (Map A B) (Map C D))
    → IsEquiv H → (g : MAP C D) → SpecializationFactorization H g
  factor-through-specialize-map H e g = record
    { factor = decode (Fact.factor named)
    ; triangle = decode-name g ∙ decode⁼
        (Fact.triangle named ∙ (H ◁ name-decode (Fact.factor named))) }
    where named = Fact.factor-through-equiv e (name g)
```
