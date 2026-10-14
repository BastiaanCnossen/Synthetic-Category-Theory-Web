# Mapping animae preserve terminal categories and products

The forward functor pairs the two postcomposition functors. Its inverse
uncurries both components on the whole product of mapping animae, pairs them,
and curries the result. No anima hypothesis is required on the domain E.
Reflection is used only at the displayed mapping anima parameters.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.MappingProducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Functoriality

module _ {Γ : Context} where
  map-terminal-contractible : (C : CAT Γ) → IsContractible (Map C One)
  map-terminal-contractible C = record
    { inverse = point
    ; left-inverse-law = uncurry-reflect (map-isAn C One)
        (id (Map C One)) (point ∘ terminate (Map C One))
        (terminal-identification _ _)
    ; right-inverse-law = terminal-identification _ _ }
    where
    point : MAP One (Map C One)
    point = mapCurry one-isAn (terminate (One × C))
```

The terminal case is `lem:Mapping_Anima_Into_Terminal_Category`. Its chosen
point names the unique functor into One. Uncurrying reflects the contraction
at the mapping anima itself, so the source category need not be an anima.

```agda
module _ {Γ : Context} where
  module ProductEquivalence (E C D : CAT Γ) where
    Source : CAT Γ
    Source = Map E (C × D)
    Target : CAT Γ
    Target = Map E C × Map E D

    target-isAn : isAn Target
    target-isAn = product-isAn (map-isAn E C) (map-isAn E D)

    forward : MAP Source Target
    forward = pair (mapPost pr₁) (mapPost pr₂)

    backward : MAP Target Source
    backward = mapCurry target-isAn (pair (uncurry pr₁) (uncurry pr₂))

    backward-β : (uncurry backward) =₁
      (pair (uncurry pr₁) (uncurry pr₂))
    backward-β = mapCurry-β target-isAn _
```

The composite on the product is identified coordinatewise, retaining both
projection comparisons.

```agda
    forward-backward-first : (mapPost pr₁ ∘ backward) =₁ pr₁
    forward-backward-first = uncurry-reflect target-isAn _ _
      (pair-β₁ (uncurry pr₁) (uncurry pr₂) ∙
        ((pr₁ ◁ backward-β) ∙ mapPost-uncurry pr₁ backward))

    forward-backward-second : (mapPost pr₂ ∘ backward) =₁ pr₂
    forward-backward-second = uncurry-reflect target-isAn _ _
      (pair-β₂ (uncurry pr₁) (uncurry pr₂) ∙
        ((pr₂ ◁ backward-β) ∙ mapPost-uncurry pr₂ backward))

    forward-backward : (forward ∘ backward) =₁ (id Target)
    forward-backward = pair₌
      ((comp-unitʳ pr₁) ⁻¹ ∙
        (forward-backward-first ∙ project-pair₁ (mapPost pr₁) (mapPost pr₂) backward))
      ((comp-unitʳ pr₂) ⁻¹ ∙
        (forward-backward-second ∙ project-pair₂ (mapPost pr₁) (mapPost pr₂) backward))
```

The other composite is identified after uncurrying at the mapping anima
Source, using the primary uncurrying action on the projection comparisons.

```agda
    substituted-pair :
      (pair (uncurry pr₁) (uncurry pr₂) ∘ productMap forward (id E)) =₁
      (pair (uncurry (mapPost pr₁)) (uncurry (mapPost pr₂)))
    substituted-pair =
      pair⁼ (uncurry⁼ (pair-β₁ (mapPost pr₁) (mapPost pr₂)))
        (uncurry⁼ (pair-β₂ (mapPost pr₁) (mapPost pr₂))) ∙
      (pair⁼ ((uncurry-restrict pr₁ forward) ⁻¹)
        ((uncurry-restrict pr₂ forward) ⁻¹) ∙
        pair-pre (uncurry pr₁) (uncurry pr₂) (productMap forward (id E)))

    backward-forward-uncurried : (uncurry (backward ∘ forward)) =₁ mapEval
    backward-forward-uncurried = pair-η mapEval ∙
      (pair⁼ (mapPost-β pr₁) (mapPost-β pr₂) ∙
      (substituted-pair ∙
      ((backward-β ▷ productMap forward (id E)) ∙ uncurry-restrict backward forward)))

    backward-forward : (backward ∘ forward) =₁ (id Source)
    backward-forward = uncurry-reflect (map-isAn E (C × D)) _ _
      ((uncurry-id E (C × D)) ⁻¹ ∙ backward-forward-uncurried)
```

The two displayed inverse comparisons give the equivalence.

```agda
    forward-isEquiv : IsEquiv forward
    forward-isEquiv = record
      { inverse = backward
      ; left-inverse-law = backward-forward ⁻¹
      ; right-inverse-law = forward-backward ⁻¹
      }
```

The public comparison is the pair of the two postcomposition maps. Its
equivalence needs no anima assumption on the testing category E.

```agda
module _ {Γ : Context} where
  mapping-product : (E C D : CAT Γ)
    → MAP (Map E (C × D)) (Map E C × Map E D)
  mapping-product = ProductEquivalence.forward

  mapping-product-isEquiv : (E C D : CAT Γ) → IsEquiv (mapping-product E C D)
  mapping-product-isEquiv = ProductEquivalence.forward-isEquiv
```
