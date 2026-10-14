# Pairing comparisons and their projections

The operations are the chosen comparisons for pairing, substitution, and
reconstruction from projections. Their laws retain the specified projection
triangles. A proof using this interface sees those operations as fields,
without unfolding their construction through a chosen inverse.

Operations and laws are separate: the operations may remain transparent in an
adapter, while their verification is opaque. The interface adds no axiom; its
realization is constructed in `ChosenPairing` under the existing assumptions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingInterface
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S

record PairingOperations : Set (c ⊔ m) where
  field
    pair-cong : {X C D : CAT} {a a′ : MAP X C} {b b′ : MAP X D}
      → a =₁ a′ → b =₁ b′ → (pair a b) =₁ (pair a′ b′)

    pair-pre : {R X C D : CAT} (a : MAP X C) (b : MAP X D) (r : MAP R X)
      → (pair a b ∘ r) =₁ (pair (a ∘ r) (b ∘ r))

    pair-projections : {C D : CAT} → (pair pr₁ pr₂) =₁ (id (C × D))

record PairingLaws (O : PairingOperations) : Set (c ⊔ m) where
  open PairingOperations O
  field
    pair-iso-extensionality : {X C D : CAT} {f g : MAP X (C × D)}
      {α β : f =₁ g}
      → (pr₁ ◁ α) =₂ (pr₁ ◁ β)
      → (pr₂ ◁ α) =₂ (pr₂ ◁ β)
      → α =₂ β

    pair-cong-triangle₁ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
      (α : f =₁ f′) (β : g =₁ g′)
      → (pair-β₁ f′ g′ ∙ (pr₁ ◁ pair-cong α β)) =₂ (α ∙ pair-β₁ f g)

    pair-cong-triangle₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
      (α : f =₁ f′) (β : g =₁ g′)
      → (pair-β₂ f′ g′ ∙ (pr₂ ◁ pair-cong α β)) =₂ (β ∙ pair-β₂ f g)

    pair-pre-triangle₁ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
      → (pair-β₁ (f ∘ σ) (g ∘ σ) ∙ (pr₁ ◁ pair-pre f g σ)) =₂
          ((pair-β₁ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₁) ⁻¹)

    pair-pre-triangle₂ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
      → (pair-β₂ (f ∘ σ) (g ∘ σ) ∙ (pr₂ ◁ pair-pre f g σ)) =₂
          ((pair-β₂ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₂) ⁻¹)

    projection-unit₁ : {C D : CAT}
      → (comp-unitʳ pr₁ ∙ (pr₁ ◁ pair-projections {C} {D})) =₂ (pair-β₁ pr₁ pr₂)

    projection-unit₂ : {C D : CAT}
      → (comp-unitʳ pr₂ ∙ (pr₂ ◁ pair-projections {C} {D})) =₂ (pair-β₂ pr₁ pr₂)
```

Product functors and their comparisons use these chosen operations. These
short formulas stay visible, including every associator in the composition
comparison. They are the original formulas, with pairing operations supplied
by the interface.

```agda
module Constructions (O : PairingOperations) where
  open PairingOperations O

  productMap : {C C′ D D′ : CAT} → MAP C C′ → MAP D D′ → MAP (C × D) (C′ × D′)
  productMap f g = pair (f ∘ pr₁) (g ∘ pr₂)

  productMap-id : (C D : CAT) → (productMap (id C) (id D)) =₁ (id (C × D))
  productMap-id C D = pair-projections ∙ pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂)

  productMap-comp : {C C′ C″ D D′ D″ : CAT}
    (f : MAP C C′) (f′ : MAP C′ C″) (g : MAP D D′) (g′ : MAP D′ D″)
    → (productMap f′ g′ ∘ productMap f g) =₁ (productMap (f′ ∘ f) (g′ ∘ g))
  productMap-comp f f′ g g′ = pair-cong
    ((comp-assoc pr₁ f f′) ⁻¹ ∙
      ((f′ ◁ pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₁ f′))
    ((comp-assoc pr₂ g g′) ⁻¹ ∙
      ((g′ ◁ pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₂ g′))
    ∙ pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) (productMap f g)

  productMap-cong : {C C′ D D′ : CAT} {f f′ : MAP C C′} {g g′ : MAP D D′}
    → f =₁ f′ → g =₁ g′ → (productMap f g) =₁ (productMap f′ g′)
  productMap-cong α β = pair-cong (α ▷ pr₁) (β ▷ pr₂)

  productMap-pair : {R C C′ D D′ : CAT}
    (f : MAP C C′) (g : MAP D D′) (u : MAP R C) (v : MAP R D)
    → (productMap f g ∘ pair u v) =₁ (pair (f ∘ u) (g ∘ v))
  productMap-pair f g u v = pair-cong
    ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
    ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g) ∙
    pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v)

  coordinate-comparison : {R X K C D : CAT}
    (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
    → (π ∘ h) =₁ (f ∘ ρ) → (F : MAP C D)
    → ((F ∘ π) ∘ h) =₁ ((F ∘ f) ∘ ρ)
  coordinate-comparison ρ f π h b F =
    (comp-assoc ρ f F) ⁻¹ ∙ ((F ◁ b) ∙ comp-assoc h π F)
```


The next interface records the already derived functoriality of those same
pairing comparisons. Its realization retains the particular higher-comparison
witness and the two ordered naturality squares.

```agda
record PairingFunctoriality (O : PairingOperations) : Set (c ⊔ m) where
  open PairingOperations O
  field
    pair-cong-comp : {X C D : CAT}
      {f₀ f₁ f₂ : MAP X C} {g₀ g₁ g₂ : MAP X D}
      (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
      (β₂ : g₁ =₁ g₂) (β₁ : g₀ =₁ g₁)
      → (pair-cong (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂
          (pair-cong α₂ β₂ ∙ pair-cong α₁ β₁)

    pair-cong-Iso₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
      {α α′ : f =₁ f′} {β β′ : g =₁ g′}
      → α =₂ α′ → β =₂ β′ → (pair-cong α β) =₂ (pair-cong α′ β′)

    pair-pre-natural-inputs : {R X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
      (α : f =₁ f′) (β : g =₁ g′) (r : MAP R X)
      → (pair-cong (α ▷ r) (β ▷ r) ∙ pair-pre f g r) =₂
          (pair-pre f′ g′ r ∙ (pair-cong α β ▷ r))

    pair-pre-natural-substitution : {R X C D : CAT}
      (f : MAP X C) (g : MAP X D) {r s : MAP R X} (γ : r =₁ s)
      → (pair-cong (f ◁ γ) (g ◁ γ) ∙ pair-pre f g r) =₂
          (pair-pre f g s ∙ (pair f g ◁ γ))

    pair-pre-iterated : {Q R X C D : CAT}
      (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R)
      → (pair-pre f g (σ ∘ τ) ∙ comp-assoc τ σ (pair f g)) =₂
          (pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g) ∙
            (pair-pre (f ∘ σ) (g ∘ σ) τ ∙ (pair-pre f g σ ▷ τ)))
```
