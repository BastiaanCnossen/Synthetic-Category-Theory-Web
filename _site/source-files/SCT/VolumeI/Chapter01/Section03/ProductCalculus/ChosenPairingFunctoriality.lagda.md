# Functoriality of the chosen pairing comparisons

The calculation interface is realized by the existing composition, higher
comparison, naturality and iteration proofs. In particular, the action on
higher comparisons retains its definition through the pairing functor on
identification animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingInterface as Interface
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairing as ChosenPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairingFunctoriality
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S)
  (PT : Coherence.PentagonTriangleCoherence V T P S) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Interface V T P S using (PairingFunctoriality)
open ChosenPairing V T P PL S VC W using (operations)
private
  module Pairing = PairingCoherence V T P PL S VC W using (pair-cong-comp; pair-cong-Iso₂)
  module Naturality = PairingNaturality V T P PL S VC W
    using (pair-pre-natural-inputs; pair-pre-natural-substitution)
  module Iteration = IteratedPairing V T P PL S VC W PT using (pair-pre-iterated)

abstract
  functoriality : PairingFunctoriality operations
  functoriality = record
    { pair-cong-comp = Pairing.pair-cong-comp
    ; pair-cong-Iso₂ = Pairing.pair-cong-Iso₂
    ; pair-pre-natural-inputs = Naturality.pair-pre-natural-inputs
    ; pair-pre-natural-substitution = Naturality.pair-pre-natural-substitution
    ; pair-pre-iterated = Iteration.pair-pre-iterated }

  composition-agreement : {X C D : CAT}
    {f₀ f₁ f₂ : MAP X C} {g₀ g₁ g₂ : MAP X D}
    (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁) (β₂ : g₁ =₁ g₂) (β₁ : g₀ =₁ g₁)
    → PairingFunctoriality.pair-cong-comp functoriality α₂ α₁ β₂ β₁ =₃
        Pairing.pair-cong-comp α₂ α₁ β₂ β₁
  composition-agreement α₂ α₁ β₂ β₁ = idIso _

  higher-comparison-agreement : {X C D : CAT}
    {f f′ : MAP X C} {g g′ : MAP X D}
    {α α′ : f =₁ f′} {β β′ : g =₁ g′}
    (p : α =₂ α′) (q : β =₂ β′)
    → PairingFunctoriality.pair-cong-Iso₂ functoriality p q =₃ Pairing.pair-cong-Iso₂ p q
  higher-comparison-agreement p q = idIso _

  input-naturality-agreement : {R X C D : CAT}
    {f f′ : MAP X C} {g g′ : MAP X D} (α : f =₁ f′) (β : g =₁ g′) (r : MAP R X)
    → PairingFunctoriality.pair-pre-natural-inputs functoriality α β r =₃
        Naturality.pair-pre-natural-inputs α β r
  input-naturality-agreement α β r = idIso _

  substitution-naturality-agreement : {R X C D : CAT}
    (f : MAP X C) (g : MAP X D) {r s : MAP R X} (γ : r =₁ s)
    → PairingFunctoriality.pair-pre-natural-substitution functoriality f g γ =₃
        Naturality.pair-pre-natural-substitution f g γ
  substitution-naturality-agreement f g γ = idIso _

  iteration-agreement : {Q R X C D : CAT}
    (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R)
    → PairingFunctoriality.pair-pre-iterated functoriality f g σ τ =₃
        Iteration.pair-pre-iterated f g σ τ
  iteration-agreement f g σ τ = idIso _
```

These agreements expose the selected proof witnesses one level higher,
without requiring consumers to unfold the law record.
