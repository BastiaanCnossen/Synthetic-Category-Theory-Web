# Inverses of identifications

Cancellation and inverse uniqueness are finite vertical calculations. They
need no whiskering coherence or pentagon. The final submodule records how
the specified inverse behaves under precomposition, using whiskering coherence.
These are the inverse witnesses used when reversing a cone's matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Specialization V T P PL S hiding (module Whiskering)
open Specialization.Units V T P PL S VC

cancel-left : {X C : CAT} {f g h : MAP X C}
  (b : g =₁ h) (α : f =₁ g)
  → (b ⁻¹ ∙ (b ∙ α)) =₂ α
cancel-left b α = isoComp-unitˡ-at α ∙
  (isoComp-cong (isoComp-inverseˡ-at b) (idIso α) ∙
    (isoComp-assoc-at (b ⁻¹) b α) ⁻¹)

cancel-right : {X C : CAT} {f g h : MAP X C}
  (a : f =₁ g) (α : g =₁ h)
  → ((α ∙ a) ∙ a ⁻¹) =₂ α
cancel-right a α = isoComp-unitʳ-at α ∙
  (isoComp-cong (idIso α) (isoComp-inverseʳ-at a) ∙
    isoComp-assoc-at α a (a ⁻¹))

cancel-left-reflect : {X C : CAT} {f g h : MAP X C}
  (b : g =₁ h) {α β : f =₁ g}
  → (b ∙ α) =₂ (b ∙ β) → α =₂ β
cancel-left-reflect b {α} {β} p = cancel-left b β ∙
  (isoComp-cong (idIso (b ⁻¹)) p ∙ (cancel-left b α) ⁻¹)

cancel-right-reflect : {X C : CAT} {f g h : MAP X C}
  (a : f =₁ g) {α β : g =₁ h}
  → (α ∙ a) =₂ (β ∙ a) → α =₂ β
cancel-right-reflect a {α} {β} p = cancel-right a β ∙
  (isoComp-cong p (idIso (a ⁻¹)) ∙ (cancel-right a α) ⁻¹)

isoInverse-unique : {C D : CAT} {f g : MAP C D}
  (α : f =₁ g) (β : g =₁ f) → (β ∙ α) =₂ (idIso f) → (α ⁻¹) =₂ β
isoInverse-unique α β p = cancel-right-reflect α (p ⁻¹ ∙ isoComp-inverseˡ-at α)

inverse-identity : {C D : CAT} (f : MAP C D) → ((idIso f) ⁻¹) =₂ (idIso f)
inverse-identity f = isoInverse-unique (idIso f) (idIso f) (isoComp-unitˡ-at (idIso f))

inverse-inverse : {C D : CAT} {f g : MAP C D} (α : f =₁ g) →
  ((α ⁻¹) ⁻¹) =₂ α
inverse-inverse α = isoInverse-unique (α ⁻¹) α (isoComp-inverseʳ-at α)

inverse-composite : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : f =₁ g) →
  ((β ∙ α) ⁻¹) =₂ (α ⁻¹ ∙ β ⁻¹)
inverse-composite β α = isoInverse-unique (β ∙ α) (α ⁻¹ ∙ β ⁻¹)
  (isoComp-inverseˡ-at α ∙
    (isoComp-cong (idIso (α ⁻¹)) (cancel-left β α) ∙
      isoComp-assoc-at (α ⁻¹) (β ⁻¹) (β ∙ α)))

```

For precomposition, apply the inverse equation and use inverse uniqueness.
This retains the same comparison used by the cone calculations.

```agda
module Whiskering (W : Coherence.WhiskeringCoherence V T P S) where
  open Coherence.WhiskeringCoherence W using (preWhisker-idIso)
  open Specialization.Whiskering V T P PL S W

  pre-inverse : {C D T : CAT} {f g : MAP C D} (α : f =₁ g) (r : MAP T C) →
    (α ⁻¹ ▷ r) =₂ ((α ▷ r) ⁻¹)
  pre-inverse {f = f} α r = (isoInverse-unique (α ▷ r) (α ⁻¹ ▷ r)
    (preWhisker-idIso f r ∙
      ((preWhisker r ◁ isoComp-inverseˡ-at α) ∙
        (preWhisker-isoComp-at (α ⁻¹) α r) ⁻¹))) ⁻¹
```
