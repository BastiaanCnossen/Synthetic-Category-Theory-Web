# Exchanging two coordinates in a nested product

The exchange of the last two coordinates of a triple product is an
equivalence. Its projection comparisons are specified explicitly, so
subsequent diagram calculations can retain their endpoint witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.NestedSymmetry
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public

exchange : {A B C : CAT} → MAP ((A × B) × C) ((A × C) × B)
exchange = pair (pair (pr₁ ∘ pr₁) pr₂) (pr₂ ∘ pr₁)

module At (A B C : CAT) where
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
    (pair-cong parameter last ∙ pair-pre (pr₁ ∘ pr₁) pr₂ forward)

  roundtrip : (exchange ∘ forward) =₁ id ((A × B) × C)
  roundtrip = pair-projections ∙
    (pair-cong first-roundtrip inner ∙
      pair-pre (pair (pr₁ ∘ pr₁) pr₂) (pr₂ ∘ pr₁) forward)

exchange-isEquiv : (A B C : CAT) → IsEquiv (exchange {A} {B} {C})
exchange-isEquiv A B C = record
  { inverse = exchange
  ; sectionIso = (At.roundtrip A B C) ⁻¹
  ; retractionIso = (At.roundtrip A C B) ⁻¹ }
```
