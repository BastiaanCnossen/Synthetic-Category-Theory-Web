# Diagrams of identifications

These records follow composition of identifications in Section 1.2.
Each diagram retains its specified higher comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section02.Diagrams
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Specialization V T P PL S

record NatIsoSquare {C D : CAT} (f g f′ g′ : MAP C D) : Set m where
  field
    top : f =₁ g
    bottom : f′ =₁ g′
    left : f =₁ f′
    right : g =₁ g′
    cell : (right ∙ top) =₂ (bottom ∙ left)

record NatIsoTriangle {C D : CAT} (f g h : MAP C D) : Set m where
  field
    first : f =₁ g
    second : g =₁ h
    diagonal : f =₁ h
    cell : diagonal =₂ (second ∙ first)

record Iso₂Square {C D : CAT} {f g : MAP C D} (α β α′ β′ : f =₁ g) : Set m where
  field
    top : α =₂ β
    bottom : α′ =₂ β′
    left : α =₂ α′
    right : β =₂ β′
    cell : (right ∙ top) =₃ (bottom ∙ left)

```
