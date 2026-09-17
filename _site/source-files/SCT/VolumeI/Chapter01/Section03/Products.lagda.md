# Mapping animae preserve products

The forward functor is the pair of postcomposition functors from the book.
The inverse is constructed over the whole product of mapping animae. The
two inverse comparisons are proved on that parameter anima, not separately
at its absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Functoriality as Functoriality

module SCT.VolumeI.Chapter01.Section03.Products
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open Functoriality 𝒯 M

private
  uncurry-cong : {X C D : CAT} {f g : MAP X (Map C D)}
    → =₁ f g → =₁ (mapUncurry f) (mapUncurry g)
  uncurry-cong {C = C} α = mapEval ◁ productMap-cong α (idIso (id C))

module ProductComparison (E C D : CAT) where
  Source = Map E (C × D)
  Target = Map E C × Map E D

  target-isAn : isAn Target
  target-isAn = product-isAn (map-isAn E C) (map-isAn E D)

  forward : MAP Source Target
  forward = pair (mapPost pr₁) (mapPost pr₂)

  backward : MAP Target Source
  backward = mapCurry target-isAn (pair (mapUncurry pr₁) (mapUncurry pr₂))

  backward-β : =₁ (mapUncurry backward)
    (pair (mapUncurry pr₁) (mapUncurry pr₂))
  backward-β = mapCurry-β target-isAn _
```

For the composite on the product, compare its two projections. In each
coordinate the beta comparison reduces the claim to the projection of a
pair, and reflection through uncurrying finishes the comparison.

```agda
  forward-backward-first : =₁ (mapPost pr₁ ∘ backward) pr₁
  forward-backward-first = mapReflect target-isAn _ _
    (pair-β₁ (mapUncurry pr₁) (mapUncurry pr₂) ∙
      ((pr₁ ◁ backward-β) ∙ mapPost-uncurry pr₁ backward))

  forward-backward-second : =₁ (mapPost pr₂ ∘ backward) pr₂
  forward-backward-second = mapReflect target-isAn _ _
    (pair-β₂ (mapUncurry pr₁) (mapUncurry pr₂) ∙
      ((pr₂ ◁ backward-β) ∙ mapPost-uncurry pr₂ backward))

  forward-backward : =₁ (forward ∘ backward) (id Target)
  forward-backward = pair-iso
    (invIso (comp-unitʳ pr₁) ∙
      (forward-backward-first ∙ project-pair₁ (mapPost pr₁) (mapPost pr₂) backward))
    (invIso (comp-unitʳ pr₂) ∙
      (forward-backward-second ∙ project-pair₂ (mapPost pr₁) (mapPost pr₂) backward))
```

For the other composite, uncurry once. Substitution into the universal
pair gives the two uncurried postcomposition functors. Their beta
comparisons identify the resulting pair with evaluation.

```agda
  substituted-pair : =₁
    (pair (mapUncurry pr₁) (mapUncurry pr₂) ∘ productMap forward (id E))
    (pair (mapUncurry (mapPost pr₁)) (mapUncurry (mapPost pr₂)))
  substituted-pair =
    pair-cong (uncurry-cong (pair-β₁ (mapPost pr₁) (mapPost pr₂)))
      (uncurry-cong (pair-β₂ (mapPost pr₁) (mapPost pr₂))) ∙
    (pair-cong (invIso (mapUncurry-pre pr₁ forward))
      (invIso (mapUncurry-pre pr₂ forward)) ∙
      pair-pre (mapUncurry pr₁) (mapUncurry pr₂) (productMap forward (id E)))

  backward-forward-uncurried : =₁ (mapUncurry (backward ∘ forward)) mapEval
  backward-forward-uncurried = pair-η mapEval ∙
    (pair-cong (mapPost-β pr₁) (mapPost-β pr₂) ∙
    (substituted-pair ∙
    ((backward-β ▷ productMap forward (id E)) ∙ mapUncurry-pre backward forward)))

  backward-forward : =₁ (backward ∘ forward) (id Source)
  backward-forward = mapReflect (map-isAn E (C × D)) _ _
    (invIso (mapUncurry-id E (C × D)) ∙ backward-forward-uncurried)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = invIso backward-forward
    ; retractionIso = invIso forward-backward
    }
```
