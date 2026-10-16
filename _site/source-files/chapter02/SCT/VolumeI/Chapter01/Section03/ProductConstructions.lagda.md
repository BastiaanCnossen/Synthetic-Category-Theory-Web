# Product equivalences and functoriality

Symmetry, a terminal factor and reassociation give chosen product equivalences.
The product functor preserves identity and composition by projection calculations.
Basic reconstruction and projection lemmas, pairing of identifications and the
elementary triple product live in Section02.Products.Calculus.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.ProductConstructions where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-inverse)
```

```agda
module _ {Γ : Context} where
  swap : {C D : CAT Γ} → MAP (C × D) (D × C)
  swap = pair pr₂ pr₁

  swap-swap : (C D : CAT Γ) → (swap ∘ swap) =₁ (id (C × D))
  swap-swap C D = pair₌
    --! begin swap-swap-first-projection
    ((comp-unitʳ pr₁) ⁻¹ ∙ (pair-β₂ pr₂ pr₁ ∙ project-pair₁ pr₂ pr₁ swap))
    --! end swap-swap-first-projection
    --! begin swap-swap-second-projection
    ((comp-unitʳ pr₂) ⁻¹ ∙ (pair-β₁ pr₂ pr₁ ∙ project-pair₂ pr₂ pr₁ swap))
    --! end swap-swap-second-projection

  swap-isEquiv : (C D : CAT Γ) → IsEquiv (swap {C = C} {D = D})
  swap-isEquiv C D = record
    { inverse = swap
    ; left-inverse-law = (swap-swap C D) ⁻¹
    ; right-inverse-law = (swap-swap D C) ⁻¹
    }
```

## The right unit

The first projection `C × One → C` has inverse given by pairing the identity
with the terminal functor. The superscript `ʳ` records that the terminal
factor is on the right. We compare the two composites by their projections.

```agda
module _ {Γ : Context} where
  product-unitʳ-inverse : (C : CAT Γ) → MAP C (C × One)
  product-unitʳ-inverse C = pair (id C) (terminate C)

  product-unitʳ-inverse-pr₁ : (C : CAT Γ)
    → (product-unitʳ-inverse C ∘ pr₁) =₁ (id (C × One))
  product-unitʳ-inverse-pr₁ C = pair₌
    --! begin product-unit-first-projection
    ((comp-unitʳ pr₁) ⁻¹ ∙
      (comp-unitˡ pr₁ ∙ project-pair₁ (id C) (terminate C) pr₁))
    --! end product-unit-first-projection
    (terminal-identification _ _)

  product-unitʳ-isEquiv : (C : CAT Γ) → IsEquiv (pr₁ {C = C} {D = One})
  product-unitʳ-isEquiv C = record
    { inverse = product-unitʳ-inverse C
    ; left-inverse-law = (product-unitʳ-inverse-pr₁ C) ⁻¹
    --! begin product-unit-retraction
    ; right-inverse-law = (pair-β₁ (id C) (terminate C)) ⁻¹
    --! end product-unit-retraction
    }
```

## The left terminal factor

The second projection has the chosen inverse inserting the terminal first
coordinate. Its two inverse identifications are kept explicit.

```agda
module _ {Γ : Context} where
  product-unitˡ-inverse : (C : CAT Γ) → MAP C (One × C)
  product-unitˡ-inverse C = pair (terminate C) (id C)

  product-unitˡ-inverse-pr₂ : (C : CAT Γ) → (product-unitˡ-inverse C ∘ pr₂) =₁ (id (One × C))
  product-unitˡ-inverse-pr₂ C = pair₌ (terminal-identification _ _)
    ((comp-unitʳ pr₂) ⁻¹ ∙
      (comp-unitˡ pr₂ ∙ project-pair₂ (terminate C) (id C) pr₂))

  product-unitˡ-pr₂-inverse : (C : CAT Γ) → (pr₂ ∘ product-unitˡ-inverse C) =₁ (id C)
  product-unitˡ-pr₂-inverse C = pair-β₂ (terminate C) (id C)

  product-unitˡ-inverse-isEquiv : (C : CAT Γ) → IsEquiv (product-unitˡ-inverse C)
  product-unitˡ-inverse-isEquiv C = record
    { inverse = pr₂
    ; left-inverse-law = (product-unitˡ-pr₂-inverse C) ⁻¹
    ; right-inverse-law = (product-unitˡ-inverse-pr₂ C) ⁻¹ }

  product-unitˡ-isEquiv : (C : CAT Γ) → IsEquiv (pr₂ {C = One} {D = C})
  product-unitˡ-isEquiv C = equiv-inverse (product-unitˡ-inverse-isEquiv C)

```

## Associativity

For associativity, each composite is reduced to the original three
projections and then reconstructed using `pair-η`. The backward functor is
the left-nested triple of the three projections, so its projection
computations are those of `Triple`.

```agda
module _ {Γ : Context} where
  module Associativity (C D E : CAT Γ) where
    forward : MAP ((C × D) × E) (C × (D × E))
    forward = pair (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)

    private
      module Backward = Triple {T = C × (D × E)} pr₁ (pr₁ ∘ pr₂) (pr₂ ∘ pr₂)

    backward : MAP (C × (D × E)) ((C × D) × E)
    backward = Backward.triple

    forward-first : (pr₁ ∘ forward) =₁ (pr₁ ∘ pr₁)
    forward-first = pair-β₁ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)

    forward-second : ((pr₁ ∘ pr₂) ∘ forward) =₁ (pr₂ ∘ pr₁)
    forward-second = pair-β₁ (pr₂ ∘ pr₁) pr₂ ∙
      ((pr₁ ◁ pair-β₂ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)) ∙
        comp-assoc forward pr₂ pr₁)

    forward-third : ((pr₂ ∘ pr₂) ∘ forward) =₁ pr₂
    forward-third = pair-β₂ (pr₂ ∘ pr₁) pr₂ ∙
      ((pr₂ ◁ pair-β₂ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)) ∙
        comp-assoc forward pr₂ pr₂)

    backward-first : ((pr₁ ∘ pr₁) ∘ backward) =₁ pr₁
    backward-first = Backward.first

    backward-second : ((pr₂ ∘ pr₁) ∘ backward) =₁ (pr₁ ∘ pr₂)
    backward-second = Backward.second

    backward-third : (pr₂ ∘ backward) =₁ (pr₂ ∘ pr₂)
    backward-third = Backward.third

    backward-forward : (backward ∘ forward) =₁ (id ((C × D) × E))
    backward-forward = pair-projections ∙
      (pair⁼ (pair-η pr₁) (id₌ pr₂) ∙
        (pair⁼
          (pair⁼ forward-first forward-second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) forward)
          forward-third ∙
          pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) forward))

    forward-backward : (forward ∘ backward) =₁ (id (C × (D × E)))
    forward-backward = pair-projections ∙
      (pair⁼ (id₌ pr₁) (pair-η pr₂) ∙
        (pair⁼ backward-first
          (pair⁼ backward-second backward-third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ backward) ∙
          pair-pre (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂) backward))

    forward-isEquiv : IsEquiv forward
    forward-isEquiv = record
      { inverse = backward
      ; left-inverse-law = backward-forward ⁻¹
      ; right-inverse-law = forward-backward ⁻¹
      }
```

## Functoriality

The product functor is the pairing from the book. Identity and composition
are compared by their two projections, with the external associators visible.

```agda
module _ {Γ : Context} where
  productMap : {C C′ D D′ : CAT Γ} → MAP C C′ → MAP D D′ → MAP (C × D) (C′ × D′)
  productMap f g = pair (f ∘ pr₁) (g ∘ pr₂)

  productMap-id : (C D : CAT Γ) → (productMap (id C) (id D)) =₁ (id (C × D))
  productMap-id C D = pair-projections ∙ pair⁼ (comp-unitˡ pr₁) (comp-unitˡ pr₂)

  productMap-comp : {C C′ C″ D D′ D″ : CAT Γ}
    (f : MAP C C′) (f′ : MAP C′ C″) (g : MAP D D′) (g′ : MAP D′ D″)
    → (productMap f′ g′ ∘ productMap f g) =₁ (productMap (f′ ∘ f) (g′ ∘ g))
  productMap-comp f f′ g g′ = pair⁼
    ((comp-assoc pr₁ f f′) ⁻¹ ∙
      ((f′ ◁ pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₁ f′))
    ((comp-assoc pr₂ g g′) ⁻¹ ∙
      ((g′ ◁ pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₂ g′))
    ∙ pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) (productMap f g)
```

## Exchanging two coordinates

The last two coordinates of a triple product can be exchanged. The three
projection identifications are kept for later diagram calculations.

```agda
module NestedSymmetry where
  module _ {Γ : Context} where
    exchange : {A B C : CAT Γ} → MAP ((A × B) × C) ((A × C) × B)
    exchange = pair (pair (pr₁ ∘ pr₁) pr₂) (pr₂ ∘ pr₁)

    module At (A B C : CAT Γ) where
      domain : MAP ((A × B) × C) (A × C)
      domain = pair (pr₁ ∘ pr₁) pr₂
      outer : MAP ((A × B) × C) B
      outer = pr₂ ∘ pr₁
      forward = exchange {A} {B} {C}

      parameter : ((pr₁ ∘ pr₁) ∘ forward) =₁ (pr₁ ∘ pr₁)
      parameter = pair-β₁ (pr₁ ∘ pr₁) pr₂ ∙
        ((pr₁ ◁ pair-β₁ domain outer) ∙ comp-assoc forward pr₁ pr₁)
      inner : ((pr₂ ∘ pr₁) ∘ forward) =₁ pr₂
      inner = pair-β₂ (pr₁ ∘ pr₁) pr₂ ∙
        ((pr₂ ◁ pair-β₁ domain outer) ∙ comp-assoc forward pr₁ pr₂)
      last : (pr₂ ∘ forward) =₁ (pr₂ ∘ pr₁)
      last = pair-β₂ domain outer

      first-roundtrip : ((pair (pr₁ ∘ pr₁) pr₂) ∘ forward) =₁ pr₁
      first-roundtrip = pair-η pr₁ ∙
        (pair⁼ parameter last ∙ pair-pre (pr₁ ∘ pr₁) pr₂ forward)

      roundtrip : (exchange ∘ forward) =₁ id ((A × B) × C)
      roundtrip = pair-projections ∙
        (pair⁼ first-roundtrip inner ∙
          pair-pre (pair (pr₁ ∘ pr₁) pr₂) (pr₂ ∘ pr₁) forward)

    exchange-isEquiv : (A B C : CAT Γ) → IsEquiv (exchange {A} {B} {C})
    exchange-isEquiv A B C = record
      { inverse = exchange
      ; left-inverse-law = (At.roundtrip A B C) ⁻¹
      ; right-inverse-law = (At.roundtrip A C B) ⁻¹ }
```

## Naturality of insertion of the terminal right factor

```agda
module _ {Γ : Context} where
  product-unitʳ-inverse-natural : {A B : CAT Γ} (f : MAP A B)
    → (productMap f (id One) ∘ product-unitʳ-inverse A) =₁
        (product-unitʳ-inverse B ∘ f)
  product-unitʳ-inverse-natural {A} {B} f = pair₌
    ((comp-unitˡ f ∙ project-pair₁ (id B) (terminate B) f) ⁻¹ ∙
      (comp-unitʳ f ∙ ((f ◁ pair-β₁ (id A) (terminate A)) ∙
        (comp-assoc (product-unitʳ-inverse A) pr₁ f ∙
          project-pair₁ (f ∘ pr₁) (id One ∘ pr₂) (product-unitʳ-inverse A)))))
    (terminal-identification _ _)
```

## Naturality of insertion of the terminal left factor

This comparison keeps the terminal identification and the chosen second
projection route.

```agda
  product-unitˡ-inverse-natural : {B C : CAT Γ} (i : MAP B C) →
    (productMap (id One) i ∘ product-unitˡ-inverse B) =₁ (product-unitˡ-inverse C ∘ i)
  product-unitˡ-inverse-natural {B} {C} i = pair₌ (terminal-identification _ _)
    ((comp-unitˡ i ∙ project-pair₂ (terminate C) (id C) i) ⁻¹ ∙
      (comp-unitʳ i ∙ ((i ◁ product-unitˡ-pr₂-inverse B) ∙
      (comp-assoc (product-unitˡ-inverse B) pr₂ i ∙
        project-pair₂ (id One ∘ pr₁) (i ∘ pr₂) (product-unitˡ-inverse B)))))
```
