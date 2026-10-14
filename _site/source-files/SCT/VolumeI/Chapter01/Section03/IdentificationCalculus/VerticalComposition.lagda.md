# Algebra of absolute identifications

The vertical composition interface needs the elementary comparison laws,
but no whiskering coherence or pentagon. This adapter is shared by generic
pasting arguments at any fixed pair of categories.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.Calculus.Composition as Algebra

module SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.VerticalComposition
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
module Original = Specialization V T P PL S
  using (isoComp-cong; module Units)
module Units = Original.Units VC
  using (isoComp-assoc-at; isoComp-unitˡ-at; isoComp-unitʳ-at)

comparisons : (X C : CAT) → Algebra.Composition m m m
comparisons X C = record
  { Obj = MAP X C; Hom = _=₁_; _≈_ = _=₂_
  ; id = idIso; _∘_ = _∙_; refl = idIso; sym = _⁻¹; trans = _∙_
  ; congr = Original.isoComp-cong }

abstract
  laws : (X C : CAT) → Algebra.Laws (comparisons X C)
  laws X C = record
    { assoc = Units.isoComp-assoc-at
    ; unitˡ = Units.isoComp-unitˡ-at; unitʳ = Units.isoComp-unitʳ-at }
```
