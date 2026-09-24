# Categories, functors, and absolute objects

The fields below are assumptions, following `post:Synthetic_Categories`.
They specify neither an inductive presentation nor Agda equality laws for
synthetic categories. Universe levels remain independent.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter01.Section01.Vocabulary where

open import Agda.Primitive using (Level; lsuc; _⊔_)

record Vocabulary (c m a : Level) : Set (lsuc (c ⊔ m ⊔ a)) where
  infixr 30 _∘_
  infix 10 _＝_
  infix 10 _=₁_ _=₂_ _=₃_
  field
    CAT : Set c
    isAn : CAT → Set a
    MAP : CAT → CAT → Set m
    id : (C : CAT) → MAP C C
    _∘_ : {C D E : CAT} → MAP D E → MAP C D → MAP C E
    One : CAT
    one-isAn : isAn One

    _＝_ : {C D : CAT} → MAP C D → MAP C D → CAT
    ＝-isAn : {C D : CAT} (f g : MAP C D) → isAn (f ＝ g)
    postWhisker : {C D E : CAT} {f g : MAP C D}
      (u : MAP D E) → MAP (f ＝ g) ((u ∘ f) ＝ (u ∘ g))
    preWhisker : {B C D : CAT} {f g : MAP C D}
      (k : MAP B C) → MAP (f ＝ g) ((f ∘ k) ＝ (g ∘ k))
    -- Inversion belongs to Section 1.2; this shared record supplies its primitive.
    ＝-inv : {C D : CAT} {f g : MAP C D} → MAP (f ＝ g) (g ＝ f)

  record AN : Set (c ⊔ a) where
    field
      category : CAT
      witness : isAn category

  Obj-abs : CAT → Set m
  Obj-abs C = MAP One C

  _=₁_ : {C D : CAT} → MAP C D → MAP C D → Set m
  f =₁ g = Obj-abs (f ＝ g)

  _=₂_ : {C D : CAT} {f g : MAP C D} → f =₁ g → f =₁ g → Set m
  α =₂ β = α =₁ β

  _=₃_ : {C D : CAT} {f g : MAP C D} {α β : f =₁ g}
    → α =₂ β → α =₂ β → Set m
  p =₃ q = p =₁ q

  record IsEquiv {C D : CAT} (f : MAP C D) : Set m where
    field
      inverse : MAP D C
      sectionIso : (id C) =₁ (inverse ∘ f)
      retractionIso : (id D) =₁ (f ∘ inverse)

  record Equiv (C D : CAT) : Set m where
    field
      functor : MAP C D
      isEquiv : IsEquiv functor
```

`Obj-abs C` means an **absolute object**, a functor from `One`. The name `Obj`
is reserved for the proposed notion of an object with an anima as parameter;
this interface does not yet bundle those parameterized objects.

Whiskering and inversion act on terms with any common parameter category.
Their source parameter is inferred from the arguments. In particular they act
on absolute natural isomorphisms, whose source is `One`.

```agda
module Operations {c m a : Level} (V : Vocabulary c m a) where
  open Vocabulary V
  infixr 35 _◁_ _▷_
  infix 40 _⁻¹

  _◁_ : {P C D E : CAT} {f g : MAP C D}
    → (u : MAP D E) → MAP P (f ＝ g) → MAP P ((u ∘ f) ＝ (u ∘ g))
  u ◁ α = postWhisker u ∘ α

  _▷_ : {P B C D : CAT} {f g : MAP C D}
    → MAP P (f ＝ g) → (k : MAP B C) → MAP P ((f ∘ k) ＝ (g ∘ k))
  α ▷ k = preWhisker k ∘ α

  _⁻¹ : {P C D : CAT} {f g : MAP C D} → MAP P (f ＝ g) → MAP P (g ＝ f)
  α ⁻¹ = ＝-inv ∘ α
```
