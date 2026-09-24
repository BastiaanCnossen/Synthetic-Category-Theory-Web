# Mapping animae preserve products

The forward functor is the pair of postcomposition functors from the book.
The inverse is constructed over the whole product of mapping animae. The
two inverse comparisons are proved on that parameter anima, not separately
at its absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Functoriality as Functoriality

module SCT.VolumeI.Chapter01.Section04.MappingProducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open Functoriality 𝒯 M

private
  uncurry-cong : {X C D : CAT} {f g : MAP X (Map C D)}
    → f =₁ g → (mapUncurry f) =₁ (mapUncurry g)
  uncurry-cong {C = C} α = mapEval ◁ productMap-cong α (idIso (id C))

```

## Constructing the two functors

The comparison sends a functor into a product to its two projections.
Conversely, uncurry the two components, pair them, and curry the result.
The following module keeps both constructions and the two inverse proofs
together.

```agda
module ProductComparison (E C D : CAT) where
  Source = Map E (C × D)
  Target = Map E C × Map E D

  target-isAn : isAn Target
  target-isAn = product-isAn (map-isAn E C) (map-isAn E D)

  forward : MAP Source Target
  forward = pair (mapPost pr₁) (mapPost pr₂)

  backward : MAP Target Source
  backward = mapCurry target-isAn (pair (mapUncurry pr₁) (mapUncurry pr₂))

  backward-β : (mapUncurry backward) =₁
    (pair (mapUncurry pr₁) (mapUncurry pr₂))
  backward-β = mapCurry-β target-isAn _
```

## The composite on the product

For the composite on the product, compare its two projections. In each
coordinate the beta comparison reduces the claim to the projection of a
pair, and reflection through uncurrying finishes the comparison.

```agda
  forward-backward-first : (mapPost pr₁ ∘ backward) =₁ pr₁
  forward-backward-first = mapReflect target-isAn _ _
    (pair-β₁ (mapUncurry pr₁) (mapUncurry pr₂) ∙
      ((pr₁ ◁ backward-β) ∙ mapPost-uncurry pr₁ backward))

  forward-backward-second : (mapPost pr₂ ∘ backward) =₁ pr₂
  forward-backward-second = mapReflect target-isAn _ _
    (pair-β₂ (mapUncurry pr₁) (mapUncurry pr₂) ∙
      ((pr₂ ◁ backward-β) ∙ mapPost-uncurry pr₂ backward))

  forward-backward : (forward ∘ backward) =₁ (id Target)
  forward-backward = pair-iso
    ((comp-unitʳ pr₁) ⁻¹ ∙
      (forward-backward-first ∙ project-pair₁ (mapPost pr₁) (mapPost pr₂) backward))
    ((comp-unitʳ pr₂) ⁻¹ ∙
      (forward-backward-second ∙ project-pair₂ (mapPost pr₁) (mapPost pr₂) backward))
```

## The other composite

For the other composite, uncurry once. Substitution into the universal
pair gives the two uncurried postcomposition functors. Their beta
comparisons identify the resulting pair with evaluation.

```agda
  substituted-pair :
    (pair (mapUncurry pr₁) (mapUncurry pr₂) ∘ productMap forward (id E)) =₁
    (pair (mapUncurry (mapPost pr₁)) (mapUncurry (mapPost pr₂)))
  substituted-pair =
    pair-cong (uncurry-cong (pair-β₁ (mapPost pr₁) (mapPost pr₂)))
      (uncurry-cong (pair-β₂ (mapPost pr₁) (mapPost pr₂))) ∙
    (pair-cong ((mapUncurry-restrict pr₁ forward) ⁻¹)
      ((mapUncurry-restrict pr₂ forward) ⁻¹) ∙
      pair-pre (mapUncurry pr₁) (mapUncurry pr₂) (productMap forward (id E)))

  backward-forward-uncurried : (mapUncurry (backward ∘ forward)) =₁ mapEval
  backward-forward-uncurried = pair-η mapEval ∙
    (pair-cong (mapPost-β pr₁) (mapPost-β pr₂) ∙
    (substituted-pair ∙
    ((backward-β ▷ productMap forward (id E)) ∙ mapUncurry-restrict backward forward)))

  backward-forward : (backward ∘ forward) =₁ (id Source)
  backward-forward = mapReflect (map-isAn E (C × D)) _ _
    ((mapUncurry-id E (C × D)) ⁻¹ ∙ backward-forward-uncurried)

```

## The equivalence

The two inverse comparisons give the equivalence asserted in the book.

```agda
  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = backward-forward ⁻¹
    ; retractionIso = forward-backward ⁻¹
    }
```
