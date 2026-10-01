# Computation of the pairing comparison

The pairing comparison was constructed using the two transported product computation witnesses. Its projections therefore compute to those witnesses by the product universal property.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as Products
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductWitnesses {l : Level} {S T : Theory l l l}
  (W : Weakening S T) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _⁻¹)
open Calculus T
open Products.Comparison W

-- Here preservation is derived: the pairing comparison was deliberately
-- constructed by lifting the two transported selected beta witnesses.
-- This does not identify arbitrary choices of pentagon or triangle witnesses.
opaque
  beta₁ : {X C D : S.CAT} (f : S.MAP X C) (g : S.MAP X D)
    → T._=₂_ (projection₁ f g) (T.pair-β₁ (map f) (map g) ∙ (T.pr₁ ◁ pairing f g))
  beta₁ f g = (isoComp-cong (T.idIso _)
      (pair-iso-β₁ ((T.pair-β₁ (map f) (map g)) ⁻¹ ∙ projection₁ f g)
        ((T.pair-β₂ (map f) (map g)) ⁻¹ ∙ projection₂ f g)) then
    (isoComp-assoc-at (T.pair-β₁ (map f) (map g)) ((T.pair-β₁ (map f) (map g)) ⁻¹) (projection₁ f g)) ⁻¹ then
    isoComp-cong (isoComp-inverseʳ-at (T.pair-β₁ (map f) (map g))) (T.idIso _) then isoComp-unitˡ-at _) ⁻¹

  beta₂ : {X C D : S.CAT} (f : S.MAP X C) (g : S.MAP X D)
    → T._=₂_ (projection₂ f g) (T.pair-β₂ (map f) (map g) ∙ (T.pr₂ ◁ pairing f g))
  beta₂ f g = (isoComp-cong (T.idIso _)
      (pair-iso-β₂ ((T.pair-β₁ (map f) (map g)) ⁻¹ ∙ projection₁ f g)
        ((T.pair-β₂ (map f) (map g)) ⁻¹ ∙ projection₂ f g)) then
    (isoComp-assoc-at (T.pair-β₂ (map f) (map g)) ((T.pair-β₂ (map f) (map g)) ⁻¹) (projection₂ f g)) ⁻¹ then
    isoComp-cong (isoComp-inverseʳ-at (T.pair-β₂ (map f) (map g))) (T.idIso _) then isoComp-unitˡ-at _) ⁻¹
```
