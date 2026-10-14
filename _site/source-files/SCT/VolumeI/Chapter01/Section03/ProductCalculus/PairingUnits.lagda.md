# Pairing and identity substitution

The identity substitution comparison agrees with the external right unitor.
The prerequisite compatibility of that unitor with composition is derived
from the primitive pentagon and triangle, rather than imposed separately.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingInterface as Interface
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairing as ChosenPairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as FunctorCoherence


module SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S)
  (PT : Coherence.PentagonTriangleCoherence V T P S) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.PentagonTriangleCoherence PT
open Specialization V T P PL S hiding (pair-cong; pair-pre)
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open PairingNaturality V T P PL S VC W using
  (cancel-left-reflect; cancel-right; project-composite)
open Structural V T P PL S W
open FunctorCoherence V T P PL S VC W PT public using
  (cancel-right-reflect; preWhisker-id-reflect; triangle-whiskered; right-unitor-comp)

module Calculation
  (O : Interface.PairingOperations V T P S)
  (L : Interface.PairingLaws V T P S O) where

  open Interface.PairingOperations O
  open Interface.PairingLaws L

  unit-square-projection : {X K C : CAT} (π : MAP K C)
    (h : MAP X K) (f : MAP X C) (b : (π ∘ h) =₁ f)
    →
        (comp-unitʳ f ∙ ((b ▷ id X) ∙ (comp-assoc (id X) h π) ⁻¹)) =₂
        (b ∙ (π ◁ comp-unitʳ h))
  unit-square-projection {X} π h f b =
    let A = comp-assoc (id X) h π
        normalize = cancel-right A (π ◁ comp-unitʳ h) ∙
          isoComp-cong (right-unitor-comp h π) (idIso (A ⁻¹))
    in isoComp-cong (idIso b) normalize ∙
      (isoComp-assoc-at b (comp-unitʳ (π ∘ h)) (A ⁻¹) ∙
      (isoComp-cong (preWhisker-id-at b) (idIso (A ⁻¹)) ∙
        (isoComp-assoc-at (comp-unitʳ f) (b ▷ id X) (A ⁻¹)) ⁻¹))

  unit-projection : {X K C : CAT} (π : MAP K C)
    (h h′ : MAP X K) (f : MAP X C)
    (b : (π ∘ h) =₁ f) (c′ : (π ∘ h′) =₁ (f ∘ id X))
    (ρ : h′ =₁ h) (τ : (h ∘ id X) =₁ h′)
    → (b ∙ (π ◁ ρ)) =₂ (comp-unitʳ f ∙ c′)
    → (c′ ∙ (π ◁ τ)) =₂ ((b ▷ id X) ∙ (comp-assoc (id X) h π) ⁻¹)
    → (π ◁ (ρ ∙ τ)) =₂ (π ◁ comp-unitʳ h)
  unit-projection π h h′ f b c′ ρ τ top bottom =
    cancel-left-reflect b
      (unit-square-projection π h f b ∙
      (isoComp-cong (idIso (comp-unitʳ f)) bottom ∙
      (isoComp-assoc-at (comp-unitʳ f) c′ (π ◁ τ) ∙
      (isoComp-cong top (idIso (π ◁ τ)) ∙ project-composite π ρ τ b))))

  pair-pre-id : {X C D : CAT} (f : MAP X C) (g : MAP X D)
    →
        (pair-cong (comp-unitʳ f) (comp-unitʳ g) ∙ pair-pre f g (id X)) =₂
        (comp-unitʳ (pair f g))
  pair-pre-id {X} f g =
    let h = pair f g
        h′ = pair (f ∘ id X) (g ∘ id X)
        ρ = pair-cong (comp-unitʳ f) (comp-unitʳ g)
        τ = pair-pre f g (id X)
    in pair-iso-extensionality
      (unit-projection pr₁ h h′ f (pair-β₁ f g) (pair-β₁ (f ∘ id X) (g ∘ id X)) ρ τ
        (pair-cong-triangle₁ (comp-unitʳ f) (comp-unitʳ g)) (pair-pre-triangle₁ f g (id X)))
      (unit-projection pr₂ h h′ g (pair-β₂ f g) (pair-β₂ (f ∘ id X) (g ∘ id X)) ρ τ
        (pair-cong-triangle₂ (comp-unitʳ f) (comp-unitʳ g)) (pair-pre-triangle₂ f g (id X)))
```

Specializing to the chosen pairing comparisons gives the identity-substitution
law with its original boundary.

```agda
private
  module Chosen = ChosenPairing V T P PL S VC W using (operations; laws)
  module Realized = Calculation Chosen.operations Chosen.laws
open Realized public hiding (pair-pre-id)
open Specialization V T P PL S using (pair-cong; pair-pre)

pair-pre-id : {X C D : CAT} (f : MAP X C) (g : MAP X D)
  →
      (pair-cong (comp-unitʳ f) (comp-unitʳ g) ∙ pair-pre f g (id X)) =₂
      (comp-unitʳ (pair f g))
pair-pre-id = Realized.pair-pre-id
```
