# Universal and arbitrary-parameter preservation

This supplements the investigation by checking restriction from the exact
four-input product. Thus the reduction to joint interchange applies to that
universal statement itself, not just to a separately assumed family version.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.Investigations.JointPreservation as Joint

module SCT.Investigations.UniversalPreservation
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
open Specialization V T P PL S
open Joint V T P PL S VC W

module Boundary {C D E : CAT}
  (f₀ f₁ f₂ : MAP C D) (g₀ g₁ g₂ : MAP D E) where
  Parameter : CAT
  Parameter = ((g₁ ＝ g₂) × (g₀ ＝ g₁)) × ((f₁ ＝ f₂) × (f₀ ＝ f₁))
  β₂ : MAP Parameter (g₁ ＝ g₂)
  β₂ = pr₁ ∘ pr₁
  β₁ : MAP Parameter (g₀ ＝ g₁)
  β₁ = pr₂ ∘ pr₁
  α₂ : MAP Parameter (f₁ ＝ f₂)
  α₂ = pr₁ ∘ pr₂
  α₁ : MAP Parameter (f₀ ＝ f₁)
  α₁ = pr₂ ∘ pr₂
  first : MAP Parameter ((g₀ ∘ f₀) ＝ (g₂ ∘ f₂))
  first = (β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)
  second : MAP Parameter ((g₀ ∘ f₀) ＝ (g₂ ∘ f₂))
  second = (β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁)

record UniversalPreservation : Set (c ⊔ m) where
  field
    preserve : {C D E : CAT} (f₀ f₁ f₂ : MAP C D) (g₀ g₁ g₂ : MAP D E)
      → =₁ (Boundary.first f₀ f₁ f₂ g₀ g₁ g₂) (Boundary.second f₀ f₁ f₂ g₀ g₁ g₂)

family-to-universal : FamilyPreservation → UniversalPreservation
family-to-universal H = record
  { preserve = λ f₀ f₁ f₂ g₀ g₁ g₂ → FamilyPreservation.preserve H
      (Boundary.β₂ f₀ f₁ f₂ g₀ g₁ g₂) (Boundary.β₁ f₀ f₁ f₂ g₀ g₁ g₂)
      (Boundary.α₂ f₀ f₁ f₂ g₀ g₁ g₂) (Boundary.α₁ f₀ f₁ f₂ g₀ g₁ g₂) }

hcomp-evaluate : {A B C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  (β : MAP B (g ＝ g′)) (α : MAP B (f ＝ f′)) (r : MAP A B)
  {β′ : MAP A (g ＝ g′)} {α′ : MAP A (f ＝ f′)}
  → =₁ (β ∘ r) β′ → =₁ (α ∘ r) α′
  → =₁ ((β ⋆ α) ∘ r) (β′ ⋆ α′)
hcomp-evaluate β α r b a = hcomp-cong b a ∙ hcomp-pre β α r

universal-to-family : UniversalPreservation → FamilyPreservation
universal-to-family H = record { preserve = restrict }
  where
  restrict : {A C D E : CAT}
    {f₀ f₁ f₂ : MAP C D} {g₀ g₁ g₂ : MAP D E}
    (β₂ : MAP A (g₁ ＝ g₂)) (β₁ : MAP A (g₀ ＝ g₁))
    (α₂ : MAP A (f₁ ＝ f₂)) (α₁ : MAP A (f₀ ＝ f₁))
    → =₁ ((β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)) ((β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁))
  restrict {f₀ = f₀} {f₁} {f₂} {g₀} {g₁} {g₂} β₂ β₁ α₂ α₁ =
    let module B = Boundary f₀ f₁ f₂ g₀ g₁ g₂
        outer = pair β₂ β₁
        inner = pair α₂ α₁
        input = pair outer inner
        outer₂ = pair-β₁ β₂ β₁ ∙ ((pr₁ ◁ pair-β₁ outer inner) ∙ comp-assoc input pr₁ pr₁)
        outer₁ = pair-β₂ β₂ β₁ ∙ ((pr₂ ◁ pair-β₁ outer inner) ∙ comp-assoc input pr₁ pr₂)
        inner₂ = pair-β₁ α₂ α₁ ∙ ((pr₁ ◁ pair-β₂ outer inner) ∙ comp-assoc input pr₂ pr₁)
        inner₁ = pair-β₂ α₂ α₁ ∙ ((pr₂ ◁ pair-β₂ outer inner) ∙ comp-assoc input pr₂ pr₂)
    in specialize (UniversalPreservation.preserve H f₀ f₁ f₂ g₀ g₁ g₂) input
      (hcomp-evaluate (B.β₂ ∙ B.β₁) (B.α₂ ∙ B.α₁) input
        (isoComp-evaluate B.β₂ B.β₁ input outer₂ outer₁)
        (isoComp-evaluate B.α₂ B.α₁ input inner₂ inner₁))
      (isoComp-evaluate (B.β₂ ⋆ B.α₂) (B.β₁ ⋆ B.α₁) input
        (hcomp-evaluate B.β₂ B.α₂ input outer₂ inner₂)
        (hcomp-evaluate B.β₁ B.α₁ input outer₁ inner₁))

universal-to-interchange : UniversalPreservation → JointInterchange
universal-to-interchange H = preservation-to-interchange (universal-to-family H)

interchange-to-universal : JointInterchange → UniversalPreservation
interchange-to-universal J = family-to-universal (Conditional.familyPreservation J)
```
