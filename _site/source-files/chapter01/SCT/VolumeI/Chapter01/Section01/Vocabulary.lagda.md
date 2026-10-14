# Categories, functors, and absolute objects

The primitives below are assumptions, following `post:Synthetic_Categories`,
available in each ambient anima context. They specify neither an inductive
presentation nor Agda equality laws for synthetic categories.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section01.Vocabulary where

open import Agda.Primitive public using (Level; _⊔_)
```

## Ambient contexts

We work in one ambient foundation. Its category, functor and anima-witness
levels are independent and fixed globally. Contexts have their own level.

```agda
postulate
  c m a κ : Level
  Context : Set κ
  absolute : Context
```

`Context` is primitive, not an inductively generated syntax. We introduce its
extension operation below, once the categorical vocabulary defines animae.

## Categories and animae

```agda

postulate
  CAT : Context → Set c

module _ {Γ : Context} where
  infixr 30 _∘_
  infix 10 _＝_

  postulate
    isAn : CAT Γ → Set a
    MAP : CAT Γ → CAT Γ → Set m
    id : (C : CAT Γ) → MAP C C
    _∘_ : {C D E : CAT Γ} → MAP D E → MAP C D → MAP C E
    One : CAT Γ
    one-isAn : isAn One

    _＝_ : {C D : CAT Γ} → MAP C D → MAP C D → CAT Γ
    ＝-isAn : {C D : CAT Γ} (f g : MAP C D) → isAn (f ＝ g)
    postWhisker : {C D E : CAT Γ} {f g : MAP C D}
      (u : MAP D E) → MAP (f ＝ g) ((u ∘ f) ＝ (u ∘ g))
    preWhisker : {B C D : CAT Γ} {f g : MAP C D}
      (k : MAP B C) → MAP (f ＝ g) ((f ∘ k) ＝ (g ∘ k))

  record AN : Set (c ⊔ a) where
    field
      category : CAT Γ
      witness : isAn category

```

Extension by an anima can be iterated using the vocabulary in the resulting
context. This declares no induction principle, weakening or substitution laws,
and imposes no strict equation on extension.

```agda
postulate
  extend : (Γ : Context) → AN {Γ} → Context
```

## Absolute objects and identifications

```agda
module _ {Γ : Context} where
  infix 10 _=₁_ _=₂_ _=₃_

  Obj-abs : CAT Γ → Set m
  Obj-abs C = MAP One C

  _=₁_ : {C D : CAT Γ} → MAP C D → MAP C D → Set m
  f =₁ g = Obj-abs (f ＝ g)

  _=₂_ : {C D : CAT Γ} {f g : MAP C D} → f =₁ g → f =₁ g → Set m
  α =₂ β = α =₁ β

  _=₃_ : {C D : CAT Γ} {f g : MAP C D} {α β : f =₁ g}
    → α =₂ β → α =₂ β → Set m
  p =₃ q = p =₁ q

  record IsEquiv {C D : CAT Γ} (f : MAP C D) : Set m where
    field
      inverse : MAP D C
      left-inverse-law : (id C) =₁ (inverse ∘ f)
      right-inverse-law : (id D) =₁ (f ∘ inverse)

  record Equiv (C D : CAT Γ) : Set m where
    field
      functor : MAP C D
      isEquiv : IsEquiv functor
```

`Obj-abs C` means an **absolute object in the ambient theory**, a functor from
its `One`. Thus it is formed in the same ambient context as `C`. The name `Obj`
is reserved for the proposed notion of an object with an anima as parameter.

Whiskering acts on families with any common parameter category. This category
is distinct from the ambient anima context. In particular, whiskering acts on
absolute natural isomorphisms, whose source is `One`.

```agda
module Operations where
  module _ {Γ : Context} where
    infixr 35 _◁_ _▷_

    _◁_ : {P C D E : CAT Γ} {f g : MAP C D}
      → (u : MAP D E) → MAP P (f ＝ g) → MAP P ((u ∘ f) ＝ (u ∘ g))
    u ◁ α = postWhisker u ∘ α

    _▷_ : {P B C D : CAT Γ} {f g : MAP C D}
      → MAP P (f ＝ g) → (k : MAP B C) → MAP P ((f ∘ k) ＝ (g ∘ k))
    α ▷ k = preWhisker k ∘ α
```

## Chosen product data

The chosen product operations and projection identifications are primitive.
Their universal-property law belongs to Section02.Products.

```agda
module _ {Γ : Context} where
  infixl 20 _×_

  postulate
    _×_ : CAT Γ → CAT Γ → CAT Γ
    pr₁ : {C D : CAT Γ} → MAP (C × D) C
    pr₂ : {C D : CAT Γ} → MAP (C × D) D
    pair : {P C D : CAT Γ} → MAP P C → MAP P D → MAP P (C × D)
    pair-β₁ : {P C D : CAT Γ} (f : MAP P C) (g : MAP P D)
      → (pr₁ ∘ pair f g) =₁ f
    pair-β₂ : {P C D : CAT Γ} (f : MAP P C) (g : MAP P D)
      → (pr₂ ∘ pair f g) =₁ g
    product-isAn : {C D : CAT Γ} → isAn C → isAn D → isAn (C × D)
```
