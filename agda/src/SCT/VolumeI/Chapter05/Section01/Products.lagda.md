# The product comparison

The comparison from a weakened product is the pair of the weakened projections. Its pairing comparison is constructed by the product universal property; preservation asks that this particular comparison be an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Products where

open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core

module Comparison {l : Level} {S T : Theory l l l} (W : Weakening S T) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)

  comparison : (C D : S.CAT) → T.MAP (cat (S._×_ C D)) (T._×_ (cat C) (cat D))
  comparison C D = T.pair (map S.pr₁) (map S.pr₂)

  projection₁ : {X C D : S.CAT} (f : S.MAP X C) (g : S.MAP X D)
    → T._=₁_ (T.pr₁ ∘ (comparison C D ∘ map (S.pair f g))) (map f)
  projection₁ {C = C} {D} f g = term (S.pair-β₁ f g) ∙
    ((comp (S.pair f g) S.pr₁) ⁻¹ ∙
    ((T.pair-β₁ (map S.pr₁) (map S.pr₂) ▷ map (S.pair f g)) ∙
    (T.comp-assoc (map (S.pair f g)) (comparison C D) T.pr₁) ⁻¹))

  projection₂ : {X C D : S.CAT} (f : S.MAP X C) (g : S.MAP X D)
    → T._=₁_ (T.pr₂ ∘ (comparison C D ∘ map (S.pair f g))) (map g)
  projection₂ {C = C} {D} f g = term (S.pair-β₂ f g) ∙
    ((comp (S.pair f g) S.pr₂) ⁻¹ ∙
    ((T.pair-β₂ (map S.pr₁) (map S.pr₂) ▷ map (S.pair f g)) ∙
    (T.comp-assoc (map (S.pair f g)) (comparison C D) T.pr₂) ⁻¹))

  pairing : {X C D : S.CAT} (f : S.MAP X C) (g : S.MAP X D)
    → T._=₁_ (comparison C D ∘ map (S.pair f g)) (T.pair (map f) (map g))
  pairing {C = C} {D} f g =
    T.IsEquiv.inverse (T.product-isoMap-isEquiv
      (comparison C D ∘ map (S.pair f g)) (T.pair (map f) (map g))) ∘
    T.pair ((T.pair-β₁ (map f) (map g)) ⁻¹ ∙ projection₁ f g)
           ((T.pair-β₂ (map f) (map g)) ⁻¹ ∙ projection₂ f g)

record PreservesProducts {l : Level} {S T : Theory l l l} (W : Weakening S T) : Set l where
  private
    module S = View S
    module T = View T
  field
    comparison-isEquiv : (C D : S.CAT) → T.IsEquiv (Comparison.comparison W C D)

compose-products : {l : Level} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S)
  → PreservesProducts V → PreservesProducts W → PreservesProducts (compose V W)
compose-products {R = R} {S} {T} V W pv pw = record
  { comparison-isEquiv = λ C D → T.equiv-transport
      (Comparison.pairing V (W.map R.pr₁) (W.map R.pr₂))
      (T.equiv-compose (V.map (Comparison.comparison W C D))
        (Comparison.comparison V (W.cat C) (W.cat D))
        (Results.preservesEquiv V (PreservesProducts.comparison-isEquiv pw C D))
        (PreservesProducts.comparison-isEquiv pv (W.cat C) (W.cat D))) }
  where
  module R = View R
  module T = View T
  module V = Weakening V
  module W = Weakening W
```
