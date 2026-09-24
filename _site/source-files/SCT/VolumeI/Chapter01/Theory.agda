{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter01.Theory where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.DerivedWhiskering as Derived

-- Shared interface for Sections 1.1 and 1.2.
-- This record collects assumptions. It does not assert that an instance exists.
record Theory (c m a : Level) : Set (lsuc (c ⊔ m ⊔ a)) where
  field
    vocabulary : Vocabulary c m a
    terminal : Terminal.TerminalStructure vocabulary
    products : Products.ProductData vocabulary
    productLaws : Products.ProductLaws vocabulary products
    composition : Coherence.CompositionStructure vocabulary terminal products
    vertical : Coherence.VerticalCoherence vocabulary terminal products composition
    whiskeringAxioms : Coherence.WhiskeringAxioms vocabulary terminal products composition
    horizontal : Coherence.HorizontalCoherence vocabulary terminal products composition
    pentagonTriangle : Coherence.PentagonTriangleCoherence vocabulary terminal products composition

  whiskering : Coherence.WhiskeringCoherence vocabulary terminal products composition
  whiskering = Derived.derivedWhiskering vocabulary terminal products productLaws
    composition vertical whiskeringAxioms horizontal
