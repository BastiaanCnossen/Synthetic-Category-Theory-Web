# Consequences for natural isomorphisms

The paragraph following the interchange axiom asserts that the derived
horizontal composite preserves identities and vertical composites. Here these
are proved for absolute natural isomorphisms between arbitrary external
functors. The arbitrary-parameter consequence of the approved joint
interchange axiom is proved separately in `Section01.JointPreservation`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section01.Isomorphisms
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W

cancel-inverse : {C D : CAT} {f g h : MAP C D}
  (β : NatIso g h) (α : NatIso f h)
  → Iso₂ (β ∙ (invIso β ∙ α)) α
cancel-inverse β α = isoComp-unitˡ-at α ∙
  (isoComp-cong (isoComp-inverseʳ-at β) (idIso α)
   ∙ invIso (isoComp-assoc-at β (invIso β) α))

reassociateFour : {C D : CAT} {f g h i j : MAP C D}
  (δ : NatIso i j) (γ : NatIso h i) (β : NatIso g h) (α : NatIso f g)
  → Iso₂ ((δ ∙ γ) ∙ (β ∙ α)) (δ ∙ ((γ ∙ β) ∙ α))
reassociateFour δ γ β α =
  isoComp-cong (idIso δ) (invIso (isoComp-assoc-at γ β α))
  ∙ isoComp-assoc-at δ γ (β ∙ α)

hcomp-idIso : {C D E : CAT} (g : MAP D E) (f : MAP C D)
  → Iso₂ (idIso g ⋆ idIso f) (idIso (g ∘ f))
hcomp-idIso g f = isoComp-unitˡ-at (idIso (g ∘ f))
  ∙ isoComp-cong (preWhisker-idIso g f) (postWhisker-idIso g f)

hcomp-interchange : {C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  (β : NatIso g g′) (α : NatIso f f′)
  → Iso₂ (β ⋆ α) ((g′ ◁ α) ∙ (β ▷ f))
hcomp-interchange = interchange-at

hcomp-isoComp : {C D E : CAT} {f₀ f₁ f₂ : MAP C D} {g₀ g₁ g₂ : MAP D E}
  (β₂ : NatIso g₁ g₂) (β₁ : NatIso g₀ g₁)
  (α₂ : NatIso f₁ f₂) (α₁ : NatIso f₀ f₁)
  → Iso₂ ((β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)) ((β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁))
hcomp-isoComp {f₁ = f₁} {f₂} {g₀ = g₀} {g₁} β₂ β₁ α₂ α₁ =
  let δ = β₂ ▷ f₂
      γ = β₁ ▷ f₂
      β = g₀ ◁ α₂
      α = g₀ ◁ α₁
      γ′ = g₁ ◁ α₂
      β′ = β₁ ▷ f₁
      expand = isoComp-cong
        (preWhisker-isoComp-at β₂ β₁ f₂)
        (postWhisker-isoComp-at g₀ α₂ α₁)
      exchange = isoComp-cong (idIso δ)
        (isoComp-cong (interchange-at β₁ α₂) (idIso α))
  in invIso (reassociateFour δ γ′ β′ α)
     ∙ (exchange ∙ (reassociateFour δ γ β α ∙ expand))
```

The fourfold reassociation is a finite pasting of the specialized vertical
associator. The middle exchange uses the derived fixed-outer restriction of
joint interchange, specialized at the indicated inner isomorphism. The proof supplies an
explicit witness and asserts no uniqueness of all possible pastings.
