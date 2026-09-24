# Pullbacks over the terminal category

The two projections give the equivalence with the product asserted in
`exercise:Pullback_Over_Terminal_Category`. Compatibility of leg comparisons
follows from the terminal axiom on isomorphism animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackProducts
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackLifting 𝒯 P

coneIso-over-One : {C D T : CAT} {f : MAP C One} {g : MAP D One}
  (s t : Cone f g T) → (Cone.left s) =₁ (Cone.left t) →
  (Cone.right s) =₁ (Cone.right t) → ConeIso s t
coneIso-over-One s t α β = record
  { leftIso = α ; rightIso = β
  ; compatible = equiv-reflect (terminalIso-isEquiv _ _) _ _ (terminal-iso _ _) }

module TerminalBase {C D : CAT} (f : MAP C One) (g : MAP D One) where

  productCone : Cone f g (C × D)
  productCone = record { left = pr₁ ; right = pr₂ ; match = terminal-iso _ _ }

  toProduct : MAP (Pullback f g) (C × D)
  toProduct = pair pullback₁ pullback₂

  fromProduct : MAP (C × D) (Pullback f g)
  fromProduct = pullbackLift productCone

  to-from : (toProduct ∘ fromProduct) =₁ (id (C × D))
  to-from = pair-projections ∙
    (pair-cong (pullbackLift-β₁ productCone) (pullbackLift-β₂ productCone) ∙ pair-pre pullback₁ pullback₂ fromProduct)

  from-to : (fromProduct ∘ toProduct) =₁ (id (Pullback f g))
  from-to = pullback-reflect _ _ (coneIso-over-One _ _
    ((comp-unitʳ pullback₁) ⁻¹ ∙
      (pair-β₁ pullback₁ pullback₂ ∙ ((pullbackLift-β₁ productCone ▷ toProduct) ∙
        (comp-assoc toProduct fromProduct pullback₁) ⁻¹)))
    ((comp-unitʳ pullback₂) ⁻¹ ∙
      (pair-β₂ pullback₁ pullback₂ ∙ ((pullbackLift-β₂ productCone ▷ toProduct) ∙
        (comp-assoc toProduct fromProduct pullback₂) ⁻¹))))

  toProduct-isEquiv : IsEquiv toProduct
  toProduct-isEquiv = record
    { inverse = fromProduct ; sectionIso = from-to ⁻¹ ; retractionIso = to-from ⁻¹ }

  productCone-isPullback : IsPullback productCone
  productCone-isPullback = record
    { inverse = toProduct ; sectionIso = to-from ⁻¹ ; retractionIso = from-to ⁻¹ }

  toSwapped : MAP (Pullback f g) (D × C)
  toSwapped = pair pullback₂ pullback₁

  fromSwapped : MAP (D × C) (Pullback f g)
  fromSwapped = fromProduct ∘ swap {D} {C}

  toSwapped-isEquiv : IsEquiv toSwapped
  toSwapped-isEquiv = equiv-transport
    (pair-cong (pair-β₂ pullback₁ pullback₂) (pair-β₁ pullback₁ pullback₂) ∙ pair-pre pr₂ pr₁ toProduct)
    (equiv-compose toProduct (swap {C} {D}) toProduct-isEquiv (swap-isEquiv C D))

  fromSwapped-isEquiv : IsEquiv fromSwapped
  fromSwapped-isEquiv = equiv-compose (swap {D} {C}) fromProduct (swap-isEquiv D C) productCone-isPullback

  fromSwapped-β₁ : (pullback₁ ∘ fromSwapped) =₁ (pr₂ {D} {C})
  fromSwapped-β₁ = pair-β₁ pr₂ pr₁ ∙
    ((pullbackLift-β₁ productCone ▷ swap {D} {C}) ∙ (comp-assoc (swap {D} {C}) fromProduct pullback₁) ⁻¹)

  fromSwapped-β₂ : (pullback₂ ∘ fromSwapped) =₁ (pr₁ {D} {C})
  fromSwapped-β₂ = pair-β₂ pr₂ pr₁ ∙
    ((pullbackLift-β₂ productCone ▷ swap {D} {C}) ∙ (comp-assoc (swap {D} {C}) fromProduct pullback₂) ⁻¹)
module PullbackProduct (C D : CAT) = TerminalBase (terminate C) (terminate D)
```
