# Pullbacks over the terminal category

The two projections give the equivalence with the product asserted in
`exercise:Pullback_Over_Terminal_Category`. Compatibility of leg comparisons
follows from the terminal axiom on isomorphism animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackProducts
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P

coneIso-over-One : {C D T : CAT} {f : MAP C One} {g : MAP D One}
  (s t : Cone f g T) → NatIso (Cone.left s) (Cone.left t) →
  NatIso (Cone.right s) (Cone.right t) → ConeIso s t
coneIso-over-One s t α β = record
  { leftIso = α ; rightIso = β
  ; compatible = equiv-reflect (terminalIso-isEquiv _ _) _ _ (terminal-iso _ _) }

module TerminalBase {C D : CAT} (f : MAP C One) (g : MAP D One) where

  productCone : Cone f g (C × D)
  productCone = record { left = pr₁ ; right = pr₂ ; match = terminal-iso _ _ }

  toProduct : MAP (Pullback f g) (C × D)
  toProduct = pair pb₁ pb₂

  fromProduct : MAP (C × D) (Pullback f g)
  fromProduct = pbLift productCone

  to-from : NatIso (toProduct ∘ fromProduct) (id (C × D))
  to-from = pair-projections ∙
    (pair-cong (pbLift-β₁ productCone) (pbLift-β₂ productCone) ∙ pair-pre pb₁ pb₂ fromProduct)

  from-to : NatIso (fromProduct ∘ toProduct) (id (Pullback f g))
  from-to = pullback-reflect _ _ (coneIso-over-One _ _
    (invIso (comp-unitʳ pb₁) ∙
      (pair-β₁ pb₁ pb₂ ∙ ((pbLift-β₁ productCone ▷ toProduct) ∙
        invIso (comp-assoc toProduct fromProduct pb₁))))
    (invIso (comp-unitʳ pb₂) ∙
      (pair-β₂ pb₁ pb₂ ∙ ((pbLift-β₂ productCone ▷ toProduct) ∙
        invIso (comp-assoc toProduct fromProduct pb₂)))))

  toProduct-isEquiv : IsEquiv toProduct
  toProduct-isEquiv = record
    { inverse = fromProduct ; sectionIso = invIso from-to ; retractionIso = invIso to-from }

  productCone-isPullback : IsPullback productCone
  productCone-isPullback = record
    { inverse = toProduct ; sectionIso = invIso to-from ; retractionIso = invIso from-to }

  toSwapped : MAP (Pullback f g) (D × C)
  toSwapped = pair pb₂ pb₁

  fromSwapped : MAP (D × C) (Pullback f g)
  fromSwapped = fromProduct ∘ swap {D} {C}

  toSwapped-isEquiv : IsEquiv toSwapped
  toSwapped-isEquiv = equiv-transport
    (pair-cong (pair-β₂ pb₁ pb₂) (pair-β₁ pb₁ pb₂) ∙ pair-pre pr₂ pr₁ toProduct)
    (equiv-compose toProduct (swap {C} {D}) toProduct-isEquiv (swap-isEquiv C D))

  fromSwapped-isEquiv : IsEquiv fromSwapped
  fromSwapped-isEquiv = equiv-compose (swap {D} {C}) fromProduct (swap-isEquiv D C) productCone-isPullback

  fromSwapped-β₁ : NatIso (pb₁ ∘ fromSwapped) (pr₂ {D} {C})
  fromSwapped-β₁ = pair-β₁ pr₂ pr₁ ∙
    ((pbLift-β₁ productCone ▷ swap {D} {C}) ∙ invIso (comp-assoc (swap {D} {C}) fromProduct pb₁))

  fromSwapped-β₂ : NatIso (pb₂ ∘ fromSwapped) (pr₁ {D} {C})
  fromSwapped-β₂ = pair-β₂ pr₂ pr₁ ∙
    ((pbLift-β₂ productCone ▷ swap {D} {C}) ∙ invIso (comp-assoc (swap {D} {C}) fromProduct pb₂))
module PullbackProduct (C D : CAT) = TerminalBase (terminate C) (terminate D)
```
