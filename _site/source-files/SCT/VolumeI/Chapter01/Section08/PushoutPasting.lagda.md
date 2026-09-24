# The pasting lemma for pushout squares

For `lem:Pasting_Lemma_Pushouts`, assume the left square is a pushout.
The right square is then a pushout if and only if the specified outer
rectangle is a pushout.

Map the diagram into an arbitrary target. The comparison below identifies
the specified outer mapping cone with the paste of the two mapping cones,
including the matching. Pullback pasting and cancellation prove the two
implications, as in the manuscript. No functor-category structure is needed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section08.PushoutPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
import SCT.VolumeI.Chapter01.Section08.PastingTransfer as Transfer
import SCT.VolumeI.Chapter01.Section08.MappingPastingComparison as Comparison

module Pasting {A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
  {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃}
  {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
  {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
  (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂)
  (left-isPushout : IsPushout left) where

  outer : Square (g₂ ∘ g₁) f₁ f₃ (h₂ ∘ h₁)
  outer = PastedSquare.outer left right

  module At (E : CAT) where
    module Diagram = Transfer.Diagram 𝒯 M P left right
    module Compared = Comparison.Diagram 𝒯 M P left right E
    open Diagram.At.WithComparison E Compared.comparison public using (paste; cancel)

  paste-isPushout : IsPushout right → IsPushout outer
  paste-isPushout right-isPushout E = At.paste E (left-isPushout E) (right-isPushout E)

  cancel-isPushout : IsPushout outer → IsPushout right
  cancel-isPushout outer-isPushout E = At.cancel E (left-isPushout E) (outer-isPushout E)
```
