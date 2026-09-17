# Products

The comparison on isomorphism animae is defined using whiskering, before
vertical or horizontal composition is introduced. Its particular functor,
rather than an unspecified equivalence with the same endpoints, receives the
universal-property witness (`post:Product_Of_Categories`).

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary

module SCT.VolumeI.Chapter01.Section01.Products
  {c m a : Level} (V : Vocabulary c m a) where

open Vocabulary V

record ProductData : Set (c ⊔ m ⊔ a) where
  infixl 20 _×_
  field
    _×_ : CAT → CAT → CAT
    pr₁ : {C D : CAT} → MAP (C × D) C
    pr₂ : {C D : CAT} → MAP (C × D) D
    pair : {P C D : CAT} → MAP P C → MAP P D → MAP P (C × D)
    pair-β₁ : {P C D : CAT} (f : MAP P C) (g : MAP P D)
      → NatIso (pr₁ ∘ pair f g) f
    pair-β₂ : {P C D : CAT} (f : MAP P C) (g : MAP P D)
      → NatIso (pr₂ ∘ pair f g) g
    product-isAn : {C D : CAT} → isAn C → isAn D → isAn (C × D)

module Comparison (P : ProductData) where
  open ProductData P

  product-isoMap : {T C D : CAT} (f g : MAP T (C × D))
    → MAP (f ≅ g) (((pr₁ ∘ f) ≅ (pr₁ ∘ g)) × ((pr₂ ∘ f) ≅ (pr₂ ∘ g)))
  product-isoMap f g = pair (postWhisker pr₁) (postWhisker pr₂)

record ProductLaws (P : ProductData) : Set (c ⊔ m) where
  open ProductData P
  open Comparison P
  field
    product-isoMap-isEquiv : {T C D : CAT} (f g : MAP T (C × D))
      → IsEquiv (product-isoMap f g)
```
