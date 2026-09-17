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
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section02.PairingNaturality
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

cancel-left : {X C : CAT} {f g h : MAP X C}
  (b : =₁ g h) (α : =₁ f g)
  → =₂ (invIso b ∙ (b ∙ α)) α
cancel-left b α = isoComp-unitˡ-at α ∙
  (isoComp-cong (isoComp-inverseˡ-at b) (idIso α) ∙
    invIso (isoComp-assoc-at (invIso b) b α))

cancel-right : {X C : CAT} {f g h : MAP X C}
  (a : =₁ f g) (α : =₁ g h)
  → =₂ ((α ∙ a) ∙ invIso a) α
cancel-right a α = isoComp-unitʳ-at α ∙
  (isoComp-cong (idIso α) (isoComp-inverseʳ-at a) ∙
    isoComp-assoc-at α a (invIso a))

cancel-left-reflect : {X C : CAT} {f g h : MAP X C}
  (b : =₁ g h) {α β : =₁ f g}
  → =₂ (b ∙ α) (b ∙ β) → =₂ α β
cancel-left-reflect b {α} {β} p = cancel-left b β ∙
  (isoComp-cong (idIso (invIso b)) p ∙ invIso (cancel-left b α))

move-square : {X C : CAT} {f g f′ g′ : MAP X C}
  (b : =₁ g g′) (u : =₁ f g) (v : =₁ f′ g′) (a : =₁ f f′)
  → =₂ (b ∙ u) (v ∙ a) → =₂ (invIso b ∙ v) (u ∙ invIso a)
move-square b u v a p =
  let solved = isoComp-cong (idIso (invIso b)) p ∙ invIso (cancel-left b u)
      rearranged = invIso (isoComp-assoc-at (invIso b) v a) ∙ solved
  in invIso (cancel-right a (invIso b ∙ v) ∙
       isoComp-cong rearranged (idIso (invIso a)))

project-composite : {X K C : CAT} {h₀ h₁ h₂ : MAP X K} {z : MAP X C}
  (π : MAP K C) (β : =₁ h₁ h₂) (α : =₁ h₀ h₁)
  (b : =₁ (π ∘ h₂) z)
  → =₂ (b ∙ (π ◁ (β ∙ α))) ((b ∙ (π ◁ β)) ∙ (π ◁ α))
project-composite π β α b = invIso (isoComp-assoc-at b (π ◁ β) (π ◁ α)) ∙
  isoComp-cong (idIso b) (postWhisker-isoComp-at π β α)
```

The first calculation is independent of products. It transports a commutative
square past a fixed substitution and accounts for the associator at a projection.

```agda
pre-square-projection : {R X K C : CAT} (π : MAP K C)
  {h h′ : MAP X K} {f f′ : MAP X C}
  (δ : =₁ h h′) (α : =₁ f f′)
  (b : =₁ (π ∘ h) f) (b′ : =₁ (π ∘ h′) f′)
  (r : MAP R X) → =₂ (b′ ∙ (π ◁ δ)) (α ∙ b)
  → =₂
      (((b′ ▷ r) ∙ invIso (comp-assoc r h′ π)) ∙ (π ◁ (δ ▷ r)))
      ((α ▷ r) ∙ ((b ▷ r) ∙ invIso (comp-assoc r h π)))
pre-square-projection π {h} {h′} δ α b b′ r square =
  let moved = move-square (comp-assoc r h′ π) ((π ◁ δ) ▷ r)
        (π ◁ (δ ▷ r)) (comp-assoc r h π) (whisker-mixed-at δ r π)
      pre-square = preWhisker-isoComp-at α b r ∙
        ((preWhisker r ◁ square) ∙ invIso (preWhisker-isoComp-at b′ (π ◁ δ) r))
  in isoComp-assoc-at (α ▷ r) (b ▷ r) (invIso (comp-assoc r h π)) ∙
    (isoComp-cong pre-square (idIso (invIso (comp-assoc r h π))) ∙
    (invIso (isoComp-assoc-at (b′ ▷ r) ((π ◁ δ) ▷ r) (invIso (comp-assoc r h π))) ∙
    (isoComp-cong (idIso (b′ ▷ r)) moved ∙
      isoComp-assoc-at (b′ ▷ r) (invIso (comp-assoc r h′ π)) (π ◁ (δ ▷ r)))))

substitution-square-projection : {R X K C : CAT} (π : MAP K C)
  (h : MAP X K) (f : MAP X C) (b : =₁ (π ∘ h) f)
  {r s : MAP R X} (γ : =₁ r s)
  → =₂
      (((b ▷ s) ∙ invIso (comp-assoc s h π)) ∙ (π ◁ (h ◁ γ)))
      ((f ◁ γ) ∙ ((b ▷ r) ∙ invIso (comp-assoc r h π)))
substitution-square-projection π h f b {r} {s} γ =
  let moved = move-square (comp-assoc s h π) ((π ∘ h) ◁ γ)
        (π ◁ (h ◁ γ)) (comp-assoc r h π) (postWhisker-comp-at γ h π)
  in isoComp-assoc-at (f ◁ γ) (b ▷ r) (invIso (comp-assoc r h π)) ∙
    (isoComp-cong (interchange-at b γ) (idIso (invIso (comp-assoc r h π))) ∙
    (invIso (isoComp-assoc-at (b ▷ s) ((π ∘ h) ◁ γ) (invIso (comp-assoc r h π))) ∙
    (isoComp-cong (idIso (b ▷ s)) moved ∙
      isoComp-assoc-at (b ▷ s) (invIso (comp-assoc s h π)) (π ◁ (h ◁ γ)))))
```

Two triangles and a projected square identify the two pastings. This helper
keeps the common target comparison explicit, so cancellation is justified.

```agda
projected-square : {X K C : CAT} {h₀ h₁ h₂ h₃ : MAP X K} {z₁ z₃ : MAP X C}
  (π : MAP K C) (ρ : =₁ h₁ h₃) (τ : =₁ h₀ h₁)
  (υ : =₁ h₂ h₃) (δ : =₁ h₀ h₂)
  (b : =₁ (π ∘ h₁) z₁) (c : =₁ (π ∘ h₃) z₃)
  (α : =₁ z₁ z₃) (q : =₁ (π ∘ h₀) z₁) (q′ : =₁ (π ∘ h₂) z₃)
  → =₂ (c ∙ (π ◁ ρ)) (α ∙ b)
  → =₂ (b ∙ (π ◁ τ)) q
  → =₂ (c ∙ (π ◁ υ)) q′
  → =₂ (q′ ∙ (π ◁ δ)) (α ∙ q)
  → =₂ (π ◁ (ρ ∙ τ)) (π ◁ (υ ∙ δ))
projected-square π ρ τ υ δ b c α q q′ top left bottom square =
  let left-normal = isoComp-cong (idIso α) left ∙
        (isoComp-assoc-at α b (π ◁ τ) ∙
          (isoComp-cong top (idIso (π ◁ τ)) ∙ project-composite π ρ τ c))
      right-normal = square ∙
        (isoComp-cong bottom (idIso (π ◁ δ)) ∙ project-composite π υ δ c)
  in cancel-left-reflect c (invIso right-normal ∙ left-normal)

pair-pre-natural-inputs : {R X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : =₁ f f′) (β : =₁ g g′) (r : MAP R X)
  → =₂ (pair-cong (α ▷ r) (β ▷ r) ∙ pair-pre f g r)
          (pair-pre f′ g′ r ∙ (pair-cong α β ▷ r))
pair-pre-natural-inputs {f = f} {f′} {g} {g′} α β r =
  let input = pair-cong α β
      output = pair-cong (α ▷ r) (β ▷ r)
      before = pair-pre f g r
      after = pair-pre f′ g′ r
  in pair-iso-extensionality
    (projected-square pr₁ output before after (input ▷ r)
      (pair-β₁ (f ∘ r) (g ∘ r)) (pair-β₁ (f′ ∘ r) (g′ ∘ r)) (α ▷ r)
      ((pair-β₁ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₁))
      ((pair-β₁ f′ g′ ▷ r) ∙ invIso (comp-assoc r (pair f′ g′) pr₁))
      (pair-cong-triangle₁ (α ▷ r) (β ▷ r))
      (pair-pre-triangle₁ f g r) (pair-pre-triangle₁ f′ g′ r)
      (pre-square-projection pr₁ input α (pair-β₁ f g) (pair-β₁ f′ g′) r
        (pair-cong-triangle₁ α β)))
    (projected-square pr₂ output before after (input ▷ r)
      (pair-β₂ (f ∘ r) (g ∘ r)) (pair-β₂ (f′ ∘ r) (g′ ∘ r)) (β ▷ r)
      ((pair-β₂ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₂))
      ((pair-β₂ f′ g′ ▷ r) ∙ invIso (comp-assoc r (pair f′ g′) pr₂))
      (pair-cong-triangle₂ (α ▷ r) (β ▷ r))
      (pair-pre-triangle₂ f g r) (pair-pre-triangle₂ f′ g′ r)
      (pre-square-projection pr₂ input β (pair-β₂ f g) (pair-β₂ f′ g′) r
        (pair-cong-triangle₂ α β)))

pair-pre-natural-substitution : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) {r s : MAP R X} (γ : =₁ r s)
  → =₂ (pair-cong (f ◁ γ) (g ◁ γ) ∙ pair-pre f g r)
          (pair-pre f g s ∙ (pair f g ◁ γ))
pair-pre-natural-substitution f g {r} {s} γ =
  let input = pair f g ◁ γ
      output = pair-cong (f ◁ γ) (g ◁ γ)
      before = pair-pre f g r
      after = pair-pre f g s
  in pair-iso-extensionality
    (projected-square pr₁ output before after input
      (pair-β₁ (f ∘ r) (g ∘ r)) (pair-β₁ (f ∘ s) (g ∘ s)) (f ◁ γ)
      ((pair-β₁ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₁))
      ((pair-β₁ f g ▷ s) ∙ invIso (comp-assoc s (pair f g) pr₁))
      (pair-cong-triangle₁ (f ◁ γ) (g ◁ γ))
      (pair-pre-triangle₁ f g r) (pair-pre-triangle₁ f g s)
      (substitution-square-projection pr₁ (pair f g) f (pair-β₁ f g) γ))
    (projected-square pr₂ output before after input
      (pair-β₂ (f ∘ r) (g ∘ r)) (pair-β₂ (f ∘ s) (g ∘ s)) (g ◁ γ)
      ((pair-β₂ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₂))
      ((pair-β₂ f g ▷ s) ∙ invIso (comp-assoc s (pair f g) pr₂))
      (pair-cong-triangle₂ (f ◁ γ) (g ◁ γ))
      (pair-pre-triangle₂ f g r) (pair-pre-triangle₂ f g s)
      (substitution-square-projection pr₂ (pair f g) g (pair-β₂ f g) γ))

pair-pre-natural : {R X C D : CAT}
  {f f′ : MAP X C} {g g′ : MAP X D} {r s : MAP R X}
  (α : =₁ f f′) (β : =₁ g g′) (γ : =₁ r s)
  → =₂ (pair-cong (α ⋆ γ) (β ⋆ γ) ∙ pair-pre f g r)
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
    (invIso (isoComp-assoc-at outer middle substitution) ∙
    (isoComp-cong (idIso outer) (pair-pre-natural-substitution f g γ) ∙
    (isoComp-assoc-at outer inner before ∙
      isoComp-cong (pair-cong-comp (α ▷ s) (f ◁ γ) (β ▷ s) (g ◁ γ)) (idIso before)))))
```
