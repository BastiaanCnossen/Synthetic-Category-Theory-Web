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
  infix 10 _≅_
  field
    CAT : Set c
    isAn : CAT → Set a
    MAP : CAT → CAT → Set m
    id : (C : CAT) → MAP C C
    _∘_ : {C D E : CAT} → MAP D E → MAP C D → MAP C E
    _≅_ : {C D : CAT} → MAP C D → MAP C D → CAT
    iso-isAn : {C D : CAT} (f g : MAP C D) → isAn (f ≅ g)
    postWhisker : {C D E : CAT} {f g : MAP C D}
      (u : MAP D E) → MAP (f ≅ g) ((u ∘ f) ≅ (u ∘ g))
    preWhisker : {B C D : CAT} {f g : MAP C D}
      (k : MAP B C) → MAP (f ≅ g) ((f ∘ k) ≅ (g ∘ k))
    isoInv : {C D : CAT} {f g : MAP C D} → MAP (f ≅ g) (g ≅ f)

    One : CAT
    one-isAn : isAn One

  record AN : Set (c ⊔ a) where
    field
      category : CAT
      witness : isAn category

  ObjAbs : CAT → Set m
  ObjAbs C = MAP One C

  NatIso : {C D : CAT} → MAP C D → MAP C D → Set m
  NatIso f g = ObjAbs (f ≅ g)

  Iso₂ : {C D : CAT} {f g : MAP C D} → NatIso f g → NatIso f g → Set m
  Iso₂ α β = NatIso α β

  Iso₃ : {C D : CAT} {f g : MAP C D} {α β : NatIso f g}
    → Iso₂ α β → Iso₂ α β → Set m
  Iso₃ p q = NatIso p q

  record IsEquiv {C D : CAT} (f : MAP C D) : Set m where
    field
      inverse : MAP D C
      sectionIso : NatIso (id C) (inverse ∘ f)
      retractionIso : NatIso (id D) (f ∘ inverse)

  record Equiv (C D : CAT) : Set m where
    field
      functor : MAP C D
      isEquiv : IsEquiv functor
```

`ObjAbs C` means an **absolute object**, a functor from `One`. The name `Obj`
is reserved for the proposed notion of an object with an anima as parameter;
this pilot does not choose its bundling convention or alter the manuscript.

Whiskering and inversion act on terms with any common parameter category.
Their source parameter is inferred from the arguments. In particular they act
on absolute natural isomorphisms, whose source is `One`.

```agda
module Operations {c m a : Level} (V : Vocabulary c m a) where
  open Vocabulary V
  infixr 35 _◁_ _▷_

  _◁_ : {P C D E : CAT} {f g : MAP C D}
    → (u : MAP D E) → MAP P (f ≅ g) → MAP P ((u ∘ f) ≅ (u ∘ g))
  u ◁ α = postWhisker u ∘ α

  _▷_ : {P B C D : CAT} {f g : MAP C D}
    → MAP P (f ≅ g) → (k : MAP B C) → MAP P ((f ∘ k) ≅ (g ∘ k))
  α ▷ k = preWhisker k ∘ α

  invIso : {P C D : CAT} {f g : MAP C D} → MAP P (f ≅ g) → MAP P (g ≅ f)
  invIso α = isoInv ∘ α
```
