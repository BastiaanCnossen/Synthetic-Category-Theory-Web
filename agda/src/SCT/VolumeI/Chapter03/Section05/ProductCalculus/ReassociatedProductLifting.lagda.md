# Prescribed comparisons after reassociating a product

The first parameter and the remaining two coordinates make an iterated
product into a product over the terminal category. Its universal
property lifts comparisons with a prescribed image on both coordinates.
In particular, the comparison on the last two coordinates is retained,
rather than inferred from an unspecified associativity isomorphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.ReassociatedProductLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackProducts 𝒯 P using (module TerminalBase; coneIso-over-One)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalConeLifting 𝒯 P using (module UniversalLift)

module Coordinates (X K S : CAT) where
  first : MAP ((X × K) × S) X
  first = pr₁ ∘ pr₁
  rest : MAP ((X × K) × S) (K × S)
  rest = productMap (pr₂ {C = X} {D = K}) (id S)
  cone : Cone (terminate X) (terminate (K × S)) ((X × K) × S)
  cone = record { left = first ; right = rest ; match = terminal-iso _ _ }
  module Product = TerminalBase (terminate X) (terminate (K × S))
  regroup = Associativity.forward X K S

  abstract
    cone-isPullback : IsPullback cone
    cone-isPullback = pullback-cone-invariant
      (coneIso-over-One (conePre regroup Product.productCone) cone
        (pair-β₁ first (pair (pr₂ ∘ pr₁) pr₂))
        (pair-cong (idIso (pr₂ ∘ pr₁)) ((comp-unitˡ pr₂) ⁻¹) ∙
          pair-β₂ first (pair (pr₂ ∘ pr₁) pr₂)))
      (pullback-restrict-equivalence Product.productCone regroup Product.productCone-isPullback
        (Associativity.forward-isEquiv X K S))

  module Lift {Y : CAT} (F G : MAP Y ((X × K) × S))
    (α : (first ∘ F) =₁ (first ∘ G)) (β : (rest ∘ F) =₁ (rest ∘ G)) where
    module Chosen = UniversalLift cone cone-isPullback F G
      (coneIso-over-One (conePre F cone) (conePre G cone) α β)
    abstract
      comparison : F =₁ G
      comparison = Chosen.lift
      first-image : (first ◁ comparison) =₂ α
      first-image = Chosen.left-image
      rest-image : (rest ◁ comparison) =₂ β
      rest-image = Chosen.right-image
```
