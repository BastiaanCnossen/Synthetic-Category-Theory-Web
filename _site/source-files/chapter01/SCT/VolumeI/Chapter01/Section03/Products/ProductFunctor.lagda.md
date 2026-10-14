# The product functor on identifications

The product functor `productMap f g = pair (f ∘ pr₁) (g ∘ pr₂)` acts on
identification families by `productMap-cong α β = pair⁼ (α ▷ pr₁) (β ▷ pr₂)`.
Individual identifications are the case of the parameter `One`. The laws of
this action are those of pairing, after prewhiskering by the projections:
congruence, composition, identities, constants, change of parameter and
squares. The universal action is the functor `productMap₌` on the product of
the identification animae.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; preWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
```

## The action and its laws

```agda
module _ {Γ : Context} where
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    productMap-cong : {C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
      → (f ＝ f′) → (g ＝ g′) → ((productMap f g) ＝ (productMap f′ g′))
    productMap-cong α β = pair⁼ (α ▷ pr₁) (β ▷ pr₂)

    productMap-cong-triangle₁ : {C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
      (α : f ＝ f′) (β : g ＝ g′)
      → SquareCell₌ (pr₁ ◁ productMap-cong α β) (α ▷ pr₁)
          (const (pair-β₁ (f ∘ pr₁) (g ∘ pr₂))) (const (pair-β₁ (f′ ∘ pr₁) (g′ ∘ pr₂)))
    productMap-cong-triangle₁ α β = pair⁼-triangle₁ (α ▷ pr₁) (β ▷ pr₂)

    productMap-cong-triangle₂ : {C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
      (α : f ＝ f′) (β : g ＝ g′)
      → SquareCell₌ (pr₂ ◁ productMap-cong α β) (β ▷ pr₂)
          (const (pair-β₂ (f ∘ pr₁) (g ∘ pr₂))) (const (pair-β₂ (f′ ∘ pr₁) (g′ ∘ pr₂)))
    productMap-cong-triangle₂ α β = pair⁼-triangle₂ (α ▷ pr₁) (β ▷ pr₂)

    productMap-cong₂ : {C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
      {α α′ : f ＝ f′} {β β′ : g ＝ g′}
      → α =₁ α′ → β =₁ β′ → productMap-cong α β =₁ productMap-cong α′ β′
    productMap-cong₂ p q = pair⁼-cong (preWhisker pr₁ ◁ p) (preWhisker pr₂ ◁ q)

    productMap-cong-comp : {C C′ D D′ : CAT Γ}
      {f₀ f₁ f₂ : MAP C C′} {g₀ g₁ g₂ : MAP D D′}
      (α₂ : f₁ ＝ f₂) (α₁ : f₀ ＝ f₁)
      (β₂ : g₁ ＝ g₂) (β₁ : g₀ ＝ g₁)
      → productMap-cong (α₂ ∙ α₁) (β₂ ∙ β₁) =₁
          (productMap-cong α₂ β₂ ∙ productMap-cong α₁ β₁)
    productMap-cong-comp α₂ α₁ β₂ β₁ =
      pair⁼-comp (α₂ ▷ pr₁) (α₁ ▷ pr₁) (β₂ ▷ pr₂) (β₁ ▷ pr₂) ∙
        pair⁼-cong (preWhisker-comp₌ α₂ α₁ pr₁) (preWhisker-comp₌ β₂ β₁ pr₂)

  productMap-cong-constant : {A C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
    (α : f =₁ f′) (β : g =₁ g′)
    → productMap-cong (const {P = A} α) (const β) =₁ const (productMap-cong α β)
  productMap-cong-constant α β = pair⁼-constant (α ▷ pr₁) (β ▷ pr₂) ∙
    pair⁼-cong (pre-constant α pr₁) (pre-constant β pr₂)

  productMap-cong-id : {A C C′ D D′ : CAT Γ} (f : MAP C C′) (g : MAP D D′)
    → productMap-cong (const {P = A} (id₌ f)) (const (id₌ g)) =₁ const (id₌ (productMap f g))
  productMap-cong-id f g = pair⁼-id (f ∘ pr₁) (g ∘ pr₂) ∙
    pair⁼-cong
      (const-cong (preWhisker-id₌ f pr₁) ∙ pre-constant (id₌ f) pr₁)
      (const-cong (preWhisker-id₌ g pr₂) ∙ pre-constant (id₌ g) pr₂)

  productMap-cong-id-One : {C C′ D D′ : CAT Γ} (f : MAP C C′) (g : MAP D D′)
    → productMap-cong (id₌ f) (id₌ g) =₂ id₌ (productMap f g)
  productMap-cong-id-One f g = pair⁼-id-One (f ∘ pr₁) (g ∘ pr₂) ∙
    pair⁼-cong (preWhisker-id₌ f pr₁) (preWhisker-id₌ g pr₂)

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    productMap-cong-square : {C C′ D D′ : CAT Γ}
      {a a′ b b′ : MAP C C′} {d d′ e e′ : MAP D D′}
      {t₁ : a ＝ b} {b₁ : a′ ＝ b′}
      {l₁ : a ＝ a′} {r₁ : b ＝ b′}
      {t₂ : d ＝ e} {b₂ : d′ ＝ e′}
      {l₂ : d ＝ d′} {r₂ : e ＝ e′}
      → SquareCell₌ t₁ b₁ l₁ r₁ → SquareCell₌ t₂ b₂ l₂ r₂
      → SquareCell₌ (productMap-cong t₁ t₂) (productMap-cong b₁ b₂)
          (productMap-cong l₁ l₂) (productMap-cong r₁ r₂)
    productMap-cong-square p q = pair⁼-square (pre-square₌ pr₁ p) (pre-square₌ pr₂ q)
```

## Change of parameter and the universal action

```agda
module _ {Γ : Context} where
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    productMap-cong-pre : {B C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
      (α : f ＝ f′) (β : g ＝ g′) (r : MAP B A)
      → (productMap-cong α β ∘ r) =₁ productMap-cong (α ∘ r) (β ∘ r)
    productMap-cong-pre α β r =
      pair⁼-cong (preWhisker-pre α pr₁ r) (preWhisker-pre β pr₂ r) ∙
        pair⁼-pre (α ▷ pr₁) (β ▷ pr₂) r

  productMap₌ : {C C′ D D′ : CAT Γ} (f f′ : MAP C C′) (g g′ : MAP D D′)
    → MAP ((Equal f f′) × (Equal g g′)) (Equal (productMap f g) (productMap f′ g′))
  productMap₌ f f′ g g′ = productMap-cong pr₁ pr₂

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    productMap₌-evaluate : {C C′ D D′ : CAT Γ} {f f′ : MAP C C′} {g g′ : MAP D D′}
      (α : f ＝ f′) (β : g ＝ g′)
      → (productMap₌ f f′ g g′ ∘ pair α β) =₁ productMap-cong α β
    productMap₌-evaluate α β =
      productMap-cong₂ (pair-β₁ α β) (pair-β₂ α β) ∙ productMap-cong-pre pr₁ pr₂ (pair α β)
```
