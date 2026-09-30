# The chosen pairing comparisons

This adapter uses the existing constructions literally. In particular,
`pair-cong`, `pair-pre`, and reconstruction from projections retain their
chosen inverse and projection witnesses. Only the proofs of the interface
laws are hidden. Neither target theorem is used to construct this adapter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence

import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductConstructions
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingInterface as Interface

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairing
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Interface V T P S
module Original = Specialization V T P PL S
  using (pair-cong; pair-pre; pair-iso-β₁; pair-iso-β₂; isoComp-cong)
open Original using (pair-iso-β₁; pair-iso-β₂; isoComp-cong)
open ProductConstructions V T P PL S using (pair-projections)
module Projections = PairingCoherence V T P PL S VC W
  using (pair-iso-extensionality; pair-cong-triangle₁; pair-cong-triangle₂;
         pair-pre-triangle₁; pair-pre-triangle₂)
open Isomorphisms V T P PL S VC W using (cancel-inverse)

operations : PairingOperations
operations = record
  { pair-cong = Original.pair-cong
  ; pair-pre = Original.pair-pre
  ; pair-projections = pair-projections }

pair-projections-triangle₁ : {C D : CAT}
  → (comp-unitʳ pr₁ ∙ (pr₁ ◁ pair-projections {C} {D})) =₂ (pair-β₁ pr₁ pr₂)
pair-projections-triangle₁ = cancel-inverse (comp-unitʳ pr₁) (pair-β₁ pr₁ pr₂) ∙
  isoComp-cong (idIso (comp-unitʳ pr₁))
    (pair-iso-β₁ ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
      ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂))

pair-projections-triangle₂ : {C D : CAT}
  → (comp-unitʳ pr₂ ∙ (pr₂ ◁ pair-projections {C} {D})) =₂ (pair-β₂ pr₁ pr₂)
pair-projections-triangle₂ = cancel-inverse (comp-unitʳ pr₂) (pair-β₂ pr₁ pr₂) ∙
  isoComp-cong (idIso (comp-unitʳ pr₂))
    (pair-iso-β₂ ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
      ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂))

abstract
  laws : PairingLaws operations
  laws = record
    { pair-iso-extensionality = Projections.pair-iso-extensionality
    ; pair-cong-triangle₁ = Projections.pair-cong-triangle₁
    ; pair-cong-triangle₂ = Projections.pair-cong-triangle₂
    ; pair-pre-triangle₁ = Projections.pair-pre-triangle₁
    ; pair-pre-triangle₂ = Projections.pair-pre-triangle₂
    ; projection-unit₁ = pair-projections-triangle₁
    ; projection-unit₂ = pair-projections-triangle₂ }

  pair-cong-triangle₁-agreement : {X C D : CAT}
    {f f′ : MAP X C} {g g′ : MAP X D} (α : f =₁ f′) (β : g =₁ g′)
    → PairingLaws.pair-cong-triangle₁ laws α β =₃ Projections.pair-cong-triangle₁ α β
  pair-cong-triangle₁-agreement α β = idIso _

  pair-cong-triangle₂-agreement : {X C D : CAT}
    {f f′ : MAP X C} {g g′ : MAP X D} (α : f =₁ f′) (β : g =₁ g′)
    → PairingLaws.pair-cong-triangle₂ laws α β =₃ Projections.pair-cong-triangle₂ α β
  pair-cong-triangle₂-agreement α β = idIso _

  pair-pre-triangle₁-agreement : {R X C D : CAT}
    (f : MAP X C) (g : MAP X D) (r : MAP R X)
    → PairingLaws.pair-pre-triangle₁ laws f g r =₃ Projections.pair-pre-triangle₁ f g r
  pair-pre-triangle₁-agreement f g r = idIso _

  pair-pre-triangle₂-agreement : {R X C D : CAT}
    (f : MAP X C) (g : MAP X D) (r : MAP R X)
    → PairingLaws.pair-pre-triangle₂ laws f g r =₃ Projections.pair-pre-triangle₂ f g r
  pair-pre-triangle₂-agreement f g r = idIso _
  projection-unit₁-agreement : {C D : CAT}
    → PairingLaws.projection-unit₁ laws {C} {D} =₃ pair-projections-triangle₁ {C} {D}
  projection-unit₁-agreement = idIso _

  projection-unit₂-agreement : {C D : CAT}
    → PairingLaws.projection-unit₂ laws {C} {D} =₃ pair-projections-triangle₂ {C} {D}
  projection-unit₂-agreement = idIso _
```

The six agreement declarations keep the supplied projection witnesses
accessible across the opacity boundary, one dimension higher. A consumer can
therefore refer to the original specified triangles without unfolding `laws`.
