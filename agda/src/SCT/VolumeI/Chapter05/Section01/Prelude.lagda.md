# The basic theory in one context

The view exposes the vocabulary and chosen structure of one theory copy. Source and target theories use the same Agda universe level throughout this chapter.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Prelude where

open import Agda.Primitive public using (Level; lsuc; _⊔_)
open import SCT.VolumeI.Chapter01.Theory public using (Theory)
import SCT.VolumeI.Chapter01.Section01.Vocabulary as Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section03.Equivalences as Equivalences

module View {l : Level} (T : Theory l l l) where
  open Theory T public
  open Vocabulary.Vocabulary vocabulary public
  open Vocabulary.Operations vocabulary public
  open Terminal.TerminalStructure terminal public
  open Terminal.Constructions vocabulary terminal public
  open Products.ProductData products public
  open Products.ProductLaws productLaws public
  open Products.Comparison vocabulary products public
  open Coherence.CompositionStructure composition public
  open Coherence.Composition vocabulary terminal products composition public
  open Coherence.VerticalCoherence vertical public
  open Coherence.WhiskeringCoherence whiskering public
  open Coherence.HorizontalCoherence horizontal public
  open Coherence.PentagonTriangleCoherence pentagonTriangle public
  open Equivalences vocabulary terminal products productLaws composition public

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
```
