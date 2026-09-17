# The language used in Section 1.3

This module gathers the preceding sections under one theory parameter. The
mathematical files can then start with their statements instead of repeating
the list of primitive structures. It introduces no axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)

module SCT.VolumeI.Chapter01.Section03.Setup
  {c m a : Level} (𝒯 : Theory c m a) where

open Theory 𝒯 public
open import SCT.VolumeI.Chapter01.Section01.Vocabulary public using (Vocabulary; module Operations)
open Vocabulary vocabulary public
open Operations vocabulary public
open import SCT.VolumeI.Chapter01.Section01.Terminal vocabulary public
  using (module TerminalStructure; module Constructions)
open TerminalStructure terminal public
open Constructions terminal public
open import SCT.VolumeI.Chapter01.Section01.Products vocabulary public
  using (module ProductData; module ProductLaws; module Comparison)
open ProductData products public
open ProductLaws productLaws public
open Comparison products public
open import SCT.VolumeI.Chapter01.Section01.Coherence vocabulary terminal products public
  using (module CompositionStructure; module Composition; module WhiskeringCoherence)
open CompositionStructure composition public
open Composition composition public
open WhiskeringCoherence whiskering public
open import SCT.VolumeI.Chapter01.Section01.Specialization vocabulary terminal products productLaws composition public
open Units vertical public
open Whiskering whiskering public
open import SCT.VolumeI.Chapter01.Section02.Equivalences vocabulary terminal products productLaws composition public
open import SCT.VolumeI.Chapter01.Section02.Products vocabulary terminal products productLaws composition public
open import SCT.VolumeI.Chapter01.Section02.ProductFunctorCoherence vocabulary terminal products productLaws composition vertical whiskering public
open import SCT.VolumeI.Chapter01.Section02.Whiskering vocabulary terminal products productLaws composition vertical whiskering public
  using (postWhisker-isEquiv; preWhisker-isEquiv; postWhisker-lift; preWhisker-lift;
         postWhisker-Iso₂-lift; preWhisker-Iso₂-lift)
```
