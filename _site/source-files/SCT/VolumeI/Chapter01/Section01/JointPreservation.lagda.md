# Joint preservation of vertical composition

The joint interchange axiom implies preservation with an arbitrary common
parameter category. This is a theorem of the accepted Section 1.1 interface;
no additional interchange hypothesis is passed to this module. The four-input
product instance is displayed at the end.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section01.JointPreservation
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.VerticalCoherence VC
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S

open Specialization.Whiskering V T P PL S W using (interchange-family)

module Triple {X A B C : CAT}
  (γ : MAP X C) (β : MAP X B) (α : MAP X A) where

  parameters : MAP X ((C × B) × A)
  parameters = pair (pair γ β) α

  first : =₁ ((pr₁ ∘ pr₁) ∘ parameters) γ
  first = pair-β₁ γ β ∙
    ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc parameters pr₁ pr₁)

  second : =₁ ((pr₂ ∘ pr₁) ∘ parameters) β
  second = pair-β₂ γ β ∙
    ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc parameters pr₁ pr₂)

  third : =₁ (pr₂ ∘ parameters) α
  third = pair-β₂ (pair γ β) α

isoComp-assoc-family : {X C D : CAT} {f g h k : MAP C D}
  (γ : MAP X (h ＝ k)) (β : MAP X (g ＝ h)) (α : MAP X (f ＝ g))
  → =₁ ((γ ∙ β) ∙ α) (γ ∙ (β ∙ α))
isoComp-assoc-family {f = f} {g} {h} {k} γ β α =
  let open Triple γ β α
  in specialize (isoComp-assoc f g h k) parameters
    (isoComp-evaluate ((pr₁ ∘ pr₁) ∙ (pr₂ ∘ pr₁)) pr₂ parameters
      (isoComp-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) parameters first second) third)
    (isoComp-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ∙ pr₂) parameters first
      (isoComp-evaluate (pr₂ ∘ pr₁) pr₂ parameters second third))

postWhisker-isoComp-family : {X C D E : CAT} {f g h : MAP C D}
  (u : MAP D E) (τ : MAP X (g ＝ h)) (σ : MAP X (f ＝ g))
  → =₁ (u ◁ (τ ∙ σ)) ((u ◁ τ) ∙ (u ◁ σ))
postWhisker-isoComp-family {f = f} {g} {h} u τ σ =
  let parameters = pair τ σ
  in specialize (postWhisker-isoComp f g h u) parameters
    (postWhisker-evaluate u (pr₁ ∙ pr₂) parameters
      (isoComp-evaluate pr₁ pr₂ parameters (pair-β₁ τ σ) (pair-β₂ τ σ)))
    (isoComp-evaluate (u ◁ pr₁) (u ◁ pr₂) parameters
      (postWhisker-evaluate u pr₁ parameters (pair-β₁ τ σ))
      (postWhisker-evaluate u pr₂ parameters (pair-β₂ τ σ)))

preWhisker-isoComp-family : {X B C D : CAT} {f g h : MAP C D}
  (τ : MAP X (g ＝ h)) (σ : MAP X (f ＝ g)) (k : MAP B C)
  → =₁ ((τ ∙ σ) ▷ k) ((τ ▷ k) ∙ (σ ▷ k))
preWhisker-isoComp-family {f = f} {g} {h} τ σ k =
  let parameters = pair τ σ
  in specialize (preWhisker-isoComp f g h k) parameters
    (preWhisker-evaluate (pr₁ ∙ pr₂) k parameters
      (isoComp-evaluate pr₁ pr₂ parameters (pair-β₁ τ σ) (pair-β₂ τ σ)))
    (isoComp-evaluate (pr₁ ▷ k) (pr₂ ▷ k) parameters
      (preWhisker-evaluate pr₁ k parameters (pair-β₁ τ σ))
      (preWhisker-evaluate pr₂ k parameters (pair-β₂ τ σ)))

reassociateFour-family : {X C D : CAT} {f g h i j : MAP C D}
  (δ : MAP X (i ＝ j)) (γ : MAP X (h ＝ i))
  (β : MAP X (g ＝ h)) (α : MAP X (f ＝ g))
  → =₁ ((δ ∙ γ) ∙ (β ∙ α)) (δ ∙ ((γ ∙ β) ∙ α))
reassociateFour-family δ γ β α =
  isoComp-cong (idIso δ) (invIso (isoComp-assoc-family γ β α))
  ∙ isoComp-assoc-family δ γ (β ∙ α)
```

Expand the two horizontal composites and exchange the middle vertical factors
using joint interchange. Both outside factors retain the same common parameter.

```agda
hcomp-isoComp-family : {X C D E : CAT}
  {f₀ f₁ f₂ : MAP C D} {g₀ g₁ g₂ : MAP D E}
  (β₂ : MAP X (g₁ ＝ g₂)) (β₁ : MAP X (g₀ ＝ g₁))
  (α₂ : MAP X (f₁ ＝ f₂)) (α₁ : MAP X (f₀ ＝ f₁))
  → =₁ ((β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)) ((β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁))
hcomp-isoComp-family {f₁ = f₁} {f₂} {g₀ = g₀} {g₁} β₂ β₁ α₂ α₁ =
  let δ = β₂ ▷ f₂
      γ = β₁ ▷ f₂
      β = g₀ ◁ α₂
      α = g₀ ◁ α₁
      γ′ = g₁ ◁ α₂
      β′ = β₁ ▷ f₁
      expand = isoComp-cong
        (preWhisker-isoComp-family β₂ β₁ f₂)
        (postWhisker-isoComp-family g₀ α₂ α₁)
      exchange = isoComp-cong (idIso δ)
        (isoComp-cong (interchange-family β₁ α₂) (idIso α))
  in invIso (reassociateFour-family δ γ′ β′ α)
     ∙ (exchange ∙ (reassociateFour-family δ γ β α ∙ expand))

module FourInputs {C D E : CAT}
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

  preserve-first : MAP Parameter ((g₀ ∘ f₀) ＝ (g₂ ∘ f₂))
  preserve-first = (β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)

  compose-first : MAP Parameter ((g₀ ∘ f₀) ＝ (g₂ ∘ f₂))
  compose-first = (β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁)

  preservation : =₁ preserve-first compose-first
  preservation = hcomp-isoComp-family β₂ β₁ α₂ α₁
```

