# Functor categories preserve products

The forward functor is the pair of postcomposition functors from the book.
The inverse is constructed over the whole product of functor categories. The
two inverse comparisons are proved on that parameter category, not separately
at its absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Currying as Currying
import SCT.VolumeI.Chapter01.Section06.Functoriality as Functoriality

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.Products
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (F : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯

open Currying 𝒯 M F
open Functoriality 𝒯 M F

private
  uncurry-cong : {X C D : CAT} {f g : MAP X (Fun C D)}
    → NatIso f g → NatIso (funUncurry f) (funUncurry g)
  uncurry-cong {C = C} α = funEval ◁ productMap-cong α (idIso (id C))

module ProductComparison (E C D : CAT) where
  Source = Fun E (C × D)
  Target = Fun E C × Fun E D


  forward : MAP Source Target
  forward = pair (funPost pr₁) (funPost pr₂)

  backward : MAP Target Source
  backward = funCurry (pair (funUncurry pr₁) (funUncurry pr₂))

  backward-β : NatIso (funUncurry backward)
    (pair (funUncurry pr₁) (funUncurry pr₂))
  backward-β = funCurry-β _
```

For the composite on the product, compare its two projections. In each
coordinate the beta comparison reduces the claim to the projection of a
pair, and reflection through uncurrying finishes the comparison.

```agda
  forward-backward-first : NatIso (funPost pr₁ ∘ backward) pr₁
  forward-backward-first = funReflect _ _
    (pair-β₁ (funUncurry pr₁) (funUncurry pr₂) ∙
      ((pr₁ ◁ backward-β) ∙ funPost-uncurry pr₁ backward))

  forward-backward-second : NatIso (funPost pr₂ ∘ backward) pr₂
  forward-backward-second = funReflect _ _
    (pair-β₂ (funUncurry pr₁) (funUncurry pr₂) ∙
      ((pr₂ ◁ backward-β) ∙ funPost-uncurry pr₂ backward))

  forward-backward : NatIso (forward ∘ backward) (id Target)
  forward-backward = pair-iso
    (invIso (comp-unitʳ pr₁) ∙
      (forward-backward-first ∙ project-pair₁ (funPost pr₁) (funPost pr₂) backward))
    (invIso (comp-unitʳ pr₂) ∙
      (forward-backward-second ∙ project-pair₂ (funPost pr₁) (funPost pr₂) backward))
```

For the other composite, uncurry once. Substitution into the universal
pair gives the two uncurried postcomposition functors. Their beta
comparisons identify the resulting pair with evaluation.

```agda
  substituted-pair : NatIso
    (pair (funUncurry pr₁) (funUncurry pr₂) ∘ productMap forward (id E))
    (pair (funUncurry (funPost pr₁)) (funUncurry (funPost pr₂)))
  substituted-pair =
    pair-cong (uncurry-cong (pair-β₁ (funPost pr₁) (funPost pr₂)))
      (uncurry-cong (pair-β₂ (funPost pr₁) (funPost pr₂))) ∙
    (pair-cong (invIso (funUncurry-pre pr₁ forward))
      (invIso (funUncurry-pre pr₂ forward)) ∙
      pair-pre (funUncurry pr₁) (funUncurry pr₂) (productMap forward (id E)))

  backward-forward-uncurried : NatIso (funUncurry (backward ∘ forward)) funEval
  backward-forward-uncurried = pair-η funEval ∙
    (pair-cong (funPost-β pr₁) (funPost-β pr₂) ∙
    (substituted-pair ∙
    ((backward-β ▷ productMap forward (id E)) ∙ funUncurry-pre backward forward)))

  backward-forward : NatIso (backward ∘ forward) (id Source)
  backward-forward = funReflect _ _
    (invIso (funUncurry-id E (C × D)) ∙ backward-forward-uncurried)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = invIso backward-forward
    ; retractionIso = invIso forward-backward
    }
```

