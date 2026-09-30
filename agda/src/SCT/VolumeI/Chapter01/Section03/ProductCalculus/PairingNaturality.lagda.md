# Naturality of pairing under precomposition

The comparison for precomposition is natural in its two functor inputs and
in the functor used for substitution. We prove the two squares separately;
their ordered pasting will give the square with all three inputs changed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses as Inverses

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
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
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open PairingCoherence V T P PL S VC W
open Structural V T P PL S W

open Inverses V T P PL S VC public using (cancel-left; cancel-right; cancel-left-reflect)

move-square : {X C : CAT} {f g f′ g′ : MAP X C}
  (b : g =₁ g′) (u : f =₁ g) (v : f′ =₁ g′) (a : f =₁ f′)
  → (b ∙ u) =₂ (v ∙ a) → (b ⁻¹ ∙ v) =₂ (u ∙ a ⁻¹)
move-square b u v a p =
  let solved = isoComp-cong (idIso (b ⁻¹)) p ∙ (cancel-left b u) ⁻¹
      rearranged = (isoComp-assoc-at (b ⁻¹) v a) ⁻¹ ∙ solved
  in (cancel-right a (b ⁻¹ ∙ v) ∙
       isoComp-cong rearranged (idIso (a ⁻¹))) ⁻¹

project-composite : {X K C : CAT} {h₀ h₁ h₂ : MAP X K} {z : MAP X C}
  (π : MAP K C) (β : h₁ =₁ h₂) (α : h₀ =₁ h₁)
  (b : (π ∘ h₂) =₁ z)
  → (b ∙ (π ◁ (β ∙ α))) =₂ ((b ∙ (π ◁ β)) ∙ (π ◁ α))
project-composite π β α b = (isoComp-assoc-at b (π ◁ β) (π ◁ α)) ⁻¹ ∙
  isoComp-cong (idIso b) (postWhisker-isoComp-at π β α)
```

The first calculation is independent of products. It transports a commutative
square past a fixed substitution and accounts for the associator at a projection.

```agda
pre-square-projection : {R X K C : CAT} (π : MAP K C)
  {h h′ : MAP X K} {f f′ : MAP X C}
  (δ : h =₁ h′) (α : f =₁ f′)
  (b : (π ∘ h) =₁ f) (b′ : (π ∘ h′) =₁ f′)
  (r : MAP R X) → (b′ ∙ (π ◁ δ)) =₂ (α ∙ b)
  →
      (((b′ ▷ r) ∙ (comp-assoc r h′ π) ⁻¹) ∙ (π ◁ (δ ▷ r))) =₂
      ((α ▷ r) ∙ ((b ▷ r) ∙ (comp-assoc r h π) ⁻¹))
pre-square-projection π {h} {h′} δ α b b′ r square =
  let moved = move-square (comp-assoc r h′ π) ((π ◁ δ) ▷ r)
        (π ◁ (δ ▷ r)) (comp-assoc r h π) (whisker-mixed-at δ r π)
      pre-square = preWhisker-isoComp-at α b r ∙
        ((preWhisker r ◁ square) ∙ (preWhisker-isoComp-at b′ (π ◁ δ) r) ⁻¹)
  in isoComp-assoc-at (α ▷ r) (b ▷ r) ((comp-assoc r h π) ⁻¹) ∙
    (isoComp-cong pre-square (idIso ((comp-assoc r h π) ⁻¹)) ∙
    ((isoComp-assoc-at (b′ ▷ r) ((π ◁ δ) ▷ r) ((comp-assoc r h π) ⁻¹)) ⁻¹ ∙
    (isoComp-cong (idIso (b′ ▷ r)) moved ∙
      isoComp-assoc-at (b′ ▷ r) ((comp-assoc r h′ π) ⁻¹) (π ◁ (δ ▷ r)))))

substitution-square-projection : {R X K C : CAT} (π : MAP K C)
  (h : MAP X K) (f : MAP X C) (b : (π ∘ h) =₁ f)
  {r s : MAP R X} (γ : r =₁ s)
  →
      (((b ▷ s) ∙ (comp-assoc s h π) ⁻¹) ∙ (π ◁ (h ◁ γ))) =₂
      ((f ◁ γ) ∙ ((b ▷ r) ∙ (comp-assoc r h π) ⁻¹))
substitution-square-projection π h f b {r} {s} γ =
  let moved = move-square (comp-assoc s h π) ((π ∘ h) ◁ γ)
        (π ◁ (h ◁ γ)) (comp-assoc r h π) (postWhisker-comp-at γ h π)
  in isoComp-assoc-at (f ◁ γ) (b ▷ r) ((comp-assoc r h π) ⁻¹) ∙
    (isoComp-cong (interchange-at b γ) (idIso ((comp-assoc r h π) ⁻¹)) ∙
    ((isoComp-assoc-at (b ▷ s) ((π ∘ h) ◁ γ) ((comp-assoc r h π) ⁻¹)) ⁻¹ ∙
    (isoComp-cong (idIso (b ▷ s)) moved ∙
      isoComp-assoc-at (b ▷ s) ((comp-assoc s h π) ⁻¹) (π ◁ (h ◁ γ)))))
```

Two triangles and a projected square identify the two pastings. This helper
keeps the common target comparison explicit, so cancellation is justified.

```agda
projected-square : {X K C : CAT} {h₀ h₁ h₂ h₃ : MAP X K} {z₁ z₃ : MAP X C}
  (π : MAP K C) (ρ : h₁ =₁ h₃) (τ : h₀ =₁ h₁)
  (υ : h₂ =₁ h₃) (δ : h₀ =₁ h₂)
  (b : (π ∘ h₁) =₁ z₁) (c : (π ∘ h₃) =₁ z₃)
  (α : z₁ =₁ z₃) (q : (π ∘ h₀) =₁ z₁) (q′ : (π ∘ h₂) =₁ z₃)
  → (c ∙ (π ◁ ρ)) =₂ (α ∙ b)
  → (b ∙ (π ◁ τ)) =₂ q
  → (c ∙ (π ◁ υ)) =₂ q′
  → (q′ ∙ (π ◁ δ)) =₂ (α ∙ q)
  → (π ◁ (ρ ∙ τ)) =₂ (π ◁ (υ ∙ δ))
projected-square π ρ τ υ δ b c α q q′ top left bottom square =
  let left-normal = isoComp-cong (idIso α) left ∙
        (isoComp-assoc-at α b (π ◁ τ) ∙
          (isoComp-cong top (idIso (π ◁ τ)) ∙ project-composite π ρ τ c))
      right-normal = square ∙
        (isoComp-cong bottom (idIso (π ◁ δ)) ∙ project-composite π υ δ c)
  in cancel-left-reflect c (right-normal ⁻¹ ∙ left-normal)

pair-pre-natural-inputs : {R X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′) (r : MAP R X)
  → (pair-cong (α ▷ r) (β ▷ r) ∙ pair-pre f g r) =₂
          (pair-pre f′ g′ r ∙ (pair-cong α β ▷ r))
pair-pre-natural-inputs {f = f} {f′} {g} {g′} α β r =
  let input = pair-cong α β
      output = pair-cong (α ▷ r) (β ▷ r)
      before = pair-pre f g r
      after = pair-pre f′ g′ r
  in pair-iso-extensionality
    (projected-square pr₁ output before after (input ▷ r)
      (pair-β₁ (f ∘ r) (g ∘ r)) (pair-β₁ (f′ ∘ r) (g′ ∘ r)) (α ▷ r)
      ((pair-β₁ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₁) ⁻¹)
      ((pair-β₁ f′ g′ ▷ r) ∙ (comp-assoc r (pair f′ g′) pr₁) ⁻¹)
      (pair-cong-triangle₁ (α ▷ r) (β ▷ r))
      (pair-pre-triangle₁ f g r) (pair-pre-triangle₁ f′ g′ r)
      (pre-square-projection pr₁ input α (pair-β₁ f g) (pair-β₁ f′ g′) r
        (pair-cong-triangle₁ α β)))
    (projected-square pr₂ output before after (input ▷ r)
      (pair-β₂ (f ∘ r) (g ∘ r)) (pair-β₂ (f′ ∘ r) (g′ ∘ r)) (β ▷ r)
      ((pair-β₂ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₂) ⁻¹)
      ((pair-β₂ f′ g′ ▷ r) ∙ (comp-assoc r (pair f′ g′) pr₂) ⁻¹)
      (pair-cong-triangle₂ (α ▷ r) (β ▷ r))
      (pair-pre-triangle₂ f g r) (pair-pre-triangle₂ f′ g′ r)
      (pre-square-projection pr₂ input β (pair-β₂ f g) (pair-β₂ f′ g′) r
        (pair-cong-triangle₂ α β)))

pair-pre-natural-substitution : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) {r s : MAP R X} (γ : r =₁ s)
  → (pair-cong (f ◁ γ) (g ◁ γ) ∙ pair-pre f g r) =₂
          (pair-pre f g s ∙ (pair f g ◁ γ))
pair-pre-natural-substitution f g {r} {s} γ =
  let input = pair f g ◁ γ
      output = pair-cong (f ◁ γ) (g ◁ γ)
      before = pair-pre f g r
      after = pair-pre f g s
  in pair-iso-extensionality
    (projected-square pr₁ output before after input
      (pair-β₁ (f ∘ r) (g ∘ r)) (pair-β₁ (f ∘ s) (g ∘ s)) (f ◁ γ)
      ((pair-β₁ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₁) ⁻¹)
      ((pair-β₁ f g ▷ s) ∙ (comp-assoc s (pair f g) pr₁) ⁻¹)
      (pair-cong-triangle₁ (f ◁ γ) (g ◁ γ))
      (pair-pre-triangle₁ f g r) (pair-pre-triangle₁ f g s)
      (substitution-square-projection pr₁ (pair f g) f (pair-β₁ f g) γ))
    (projected-square pr₂ output before after input
      (pair-β₂ (f ∘ r) (g ∘ r)) (pair-β₂ (f ∘ s) (g ∘ s)) (g ◁ γ)
      ((pair-β₂ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₂) ⁻¹)
      ((pair-β₂ f g ▷ s) ∙ (comp-assoc s (pair f g) pr₂) ⁻¹)
      (pair-cong-triangle₂ (f ◁ γ) (g ◁ γ))
      (pair-pre-triangle₂ f g r) (pair-pre-triangle₂ f g s)
      (substitution-square-projection pr₂ (pair f g) g (pair-β₂ f g) γ))

pair-pre-natural : {R X C D : CAT}
  {f f′ : MAP X C} {g g′ : MAP X D} {r s : MAP R X}
  (α : f =₁ f′) (β : g =₁ g′) (γ : r =₁ s)
  → (pair-cong (α ⋆ γ) (β ⋆ γ) ∙ pair-pre f g r) =₂
          (pair-pre f′ g′ s ∙ (pair-cong α β ⋆ γ))
pair-pre-natural {f = f} {f′} {g} {g′} {r} {s} α β γ =
  let outer = pair-cong (α ▷ s) (β ▷ s)
      inner = pair-cong (f ◁ γ) (g ◁ γ)
      before = pair-pre f g r
      middle = pair-pre f g s
      after = pair-pre f′ g′ s
      input = pair-cong α β ▷ s
      substitution = pair f g ◁ γ
  in isoComp-assoc-at after input substitution ∙
    (isoComp-cong (pair-pre-natural-inputs α β s) (idIso substitution) ∙
    ((isoComp-assoc-at outer middle substitution) ⁻¹ ∙
    (isoComp-cong (idIso outer) (pair-pre-natural-substitution f g γ) ∙
    (isoComp-assoc-at outer inner before ∙
      isoComp-cong (pair-cong-comp (α ▷ s) (f ◁ γ) (β ▷ s) (g ◁ γ)) (idIso before)))))
```
