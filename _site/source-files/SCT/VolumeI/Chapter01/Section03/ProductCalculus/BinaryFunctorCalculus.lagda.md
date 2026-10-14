# Binary functors and restriction

A functor from a product acts on two functors with a common parameter.
Pairing and postcomposition give its action on identifications and its
restriction comparison. The naturality squares below are independent of
mapping animae; evaluation will be one instance.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateNaturality as CoordinateNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateComparisons as CoordinateComparisons

import SCT.Calculus.Squares as Squares
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.VerticalComposition as VerticalComposition

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.BinaryFunctorCalculus
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
open Structural V T P PL S W using (whisker-mixed-at; postWhisker-comp-at)
open PairingCoherence V T P PL S VC W using (pair-cong-comp; pair-cong-Iso₂)
open PairingNaturality V T P PL S VC W
  using (pair-pre-natural-inputs; pair-pre-natural-substitution)
open CoordinateNaturality V T P PL S VC W using (post-square; paste-squares)

private
  module Vertical = VerticalComposition V T P PL S VC
  module Paste (X Y : CAT) = Squares (Vertical.comparisons X Y)
    (record { assoc = isoComp-assoc-at; unitˡ = isoComp-unitˡ-at; unitʳ = isoComp-unitʳ-at })

binaryApply : {X A B C : CAT} → MAP (A × B) C → MAP X A → MAP X B → MAP X C
binaryApply F f x = F ∘ pair f x

binaryCong : {X A B C : CAT} (F : MAP (A × B) C)
  {f g : MAP X A} {x y : MAP X B}
  → f =₁ g → x =₁ y → (binaryApply F f x) =₁ (binaryApply F g y)
binaryCong F α β = F ◁ pair-cong α β

binaryPre : {X Y A B C : CAT} (F : MAP (A × B) C)
  (f : MAP X A) (x : MAP X B) (r : MAP Y X)
  → (binaryApply F f x ∘ r) =₁ (binaryApply F (f ∘ r) (x ∘ r))
binaryPre F f x r = (F ◁ pair-pre f x r) ∙ comp-assoc r (pair f x) F

binary-cong-comp : {X A B C : CAT} (F : MAP (A × B) C)
  {f₀ f₁ f₂ : MAP X A} {x₀ x₁ x₂ : MAP X B}
  (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
  (β₂ : x₁ =₁ x₂) (β₁ : x₀ =₁ x₁)
  → (binaryCong F (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂
      (binaryCong F α₂ β₂ ∙ binaryCong F α₁ β₁)
binary-cong-comp F α₂ α₁ β₂ β₁ =
  postWhisker-isoComp-at F (pair-cong α₂ β₂) (pair-cong α₁ β₁) ∙
    (postWhisker F ◁ pair-cong-comp α₂ α₁ β₂ β₁)

binary-cong-Iso₂ : {X A B C : CAT} (F : MAP (A × B) C)
  {f f′ : MAP X A} {x x′ : MAP X B}
  {α α′ : f =₁ f′} {β β′ : x =₁ x′}
  → α =₂ α′ → β =₂ β′
  → (binaryCong F α β) =₂ (binaryCong F α′ β′)
binary-cong-Iso₂ F p q = postWhisker F ◁ pair-cong-Iso₂ p q

binary-pre-inputs : {X Y A B C : CAT} (F : MAP (A × B) C)
  {f f′ : MAP X A} {g g′ : MAP X B}
  (α : f =₁ f′) (β : g =₁ g′) (r : MAP Y X)
  → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
        after = (F ◁ pair-pre f′ g′ r) ∙ comp-assoc r (pair f′ g′) F
    in (after ∙ ((F ◁ pair-cong α β) ▷ r)) =₂
        ((F ◁ pair-cong (α ▷ r) (β ▷ r)) ∙ before)
binary-pre-inputs F {f} {f′} {g} {g′} α β r =
  paste-squares (comp-assoc r (pair f g) F) (comp-assoc r (pair f′ g′) F)
    (F ◁ pair-pre f g r) (F ◁ pair-pre f′ g′ r)
    ((F ◁ pair-cong α β) ▷ r) (F ◁ (pair-cong α β ▷ r))
    (F ◁ pair-cong (α ▷ r) (β ▷ r))
    (whisker-mixed-at (pair-cong α β) r F)
    (post-square F (pair-pre f g r) (pair-pre f′ g′ r)
      (pair-cong α β ▷ r) (pair-cong (α ▷ r) (β ▷ r))
      ((pair-pre-natural-inputs α β r) ⁻¹))

binary-pre-substitution : {X Y A B C : CAT} (F : MAP (A × B) C)
  (f : MAP X A) (g : MAP X B) {r s : MAP Y X} (γ : r =₁ s)
  → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
        after = (F ◁ pair-pre f g s) ∙ comp-assoc s (pair f g) F
    in (after ∙ ((F ∘ pair f g) ◁ γ)) =₂
        ((F ◁ pair-cong (f ◁ γ) (g ◁ γ)) ∙ before)
binary-pre-substitution F f g {r} {s} γ =
  paste-squares (comp-assoc r (pair f g) F) (comp-assoc s (pair f g) F)
    (F ◁ pair-pre f g r) (F ◁ pair-pre f g s)
    ((F ∘ pair f g) ◁ γ) (F ◁ (pair f g ◁ γ))
    (F ◁ pair-cong (f ◁ γ) (g ◁ γ))
    (postWhisker-comp-at γ (pair f g) F)
    (post-square F (pair-pre f g r) (pair-pre f g s)
      (pair f g ◁ γ) (pair-cong (f ◁ γ) (g ◁ γ))
      ((pair-pre-natural-substitution f g γ) ⁻¹))

binary-combine : {X A B C : CAT} (F : MAP (A × B) C)
  {f₀ f₁ f₂ : MAP X A} {x₀ x₁ x₂ : MAP X B} {source : MAP X C}
  (α : f₁ =₁ f₂) (β : x₁ =₁ x₂)
  (γ : f₀ =₁ f₁) (δ : x₀ =₁ x₁)
  (base : source =₁ (binaryApply F f₀ x₀))
  → (binaryCong F α β ∙ (binaryCong F γ δ ∙ base)) =₂
      (binaryCong F (α ∙ γ) (β ∙ δ) ∙ base)
binary-combine F α β γ δ base =
  isoComp-cong ((binary-cong-comp F α γ β δ) ⁻¹) (idIso base) ∙
    (isoComp-assoc-at (binaryCong F α β) (binaryCong F γ δ) base) ⁻¹

```

The pentagon is used only for iterated restriction. A normalized binary
application is a restriction followed by comparisons of its two inputs.
Normalize both routes, then use their specified input squares.

```agda
module Iteration (PT : Coherence.PentagonTriangleCoherence V T P S) where
  open IteratedPairing V T P PL S VC W PT using (pair-pre-iterated)
  open CoordinateComparisons V T P PL S VC W PT using (post-iterated-comparison)

  binary-pre-iterated : {Q R X A B C : CAT}
    (F : MAP (A × B) C) (f : MAP X A) (x : MAP X B)
    (σ : MAP R X) (τ : MAP Q R)
    → let pre : {Y Z : CAT} (g : MAP Y A) (y : MAP Y B) (r : MAP Z Y)
              → ((F ∘ pair g y) ∘ r) =₁ (F ∘ pair (g ∘ r) (y ∘ r))
          pre g y r = (F ◁ pair-pre g y r) ∙ comp-assoc r (pair g y) F
      in (pre f x (σ ∘ τ) ∙ comp-assoc τ σ (F ∘ pair f x)) =₂
        ((F ◁ pair-cong (comp-assoc τ σ f) (comp-assoc τ σ x)) ∙
          (pre (f ∘ σ) (x ∘ σ) τ ∙ (pre f x σ ▷ τ)))
  binary-pre-iterated F f x σ τ = post-iterated-comparison F (pair f x) σ τ
    (pair-pre f x σ) (pair-pre (f ∘ σ) (x ∘ σ) τ) (pair-pre f x (σ ∘ τ))
    (pair-cong (comp-assoc τ σ f) (comp-assoc τ σ x)) (pair-pre-iterated f x σ τ)

  module Assembly {R Γ X A B C : CAT} (F : MAP (A × B) C)
    (H : MAP X A) (K : MAP X B)
    (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : (q ∘ r) =₁ q′)
    {f : MAP Γ A} {x : MAP Γ B}
    {f′ : MAP R A} {x′ : MAP R B}
    (a : (H ∘ q) =₁ f) (b : (K ∘ q) =₁ x)
    (a′ : (H ∘ q′) =₁ f′) (b′ : (K ∘ q′) =₁ x′)
    (c : (f ∘ r) =₁ f′) (d : (x ∘ r) =₁ x′) where

    normalization = binaryCong F a b ∙ binaryPre F H K q
    normalization′ = binaryCong F a′ b′ ∙ binaryPre F H K q′

    short = normalization′ ∙ ((binaryApply F H K ◁ δ) ∙ comp-assoc r q (binaryApply F H K))
    long = binaryCong F c d ∙ (binaryPre F f x r ∙ (normalization ▷ r))

    base = binaryPre F (H ∘ q) (K ∘ q) r ∙ (binaryPre F H K q ▷ r)

    short-normalization : short =₂
      (binaryCong F (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H))
        (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) ∙ base)
    short-normalization =
      Paste.normalized-substitution-square R C
        (binaryCong F a′ b′) (binaryPre F H K q′) (binaryApply F H K ◁ δ)
        (comp-assoc r q (binaryApply F H K)) (binaryCong F (H ◁ δ) (K ◁ δ))
        (binaryPre F H K (q ∘ r)) (binaryCong F (comp-assoc r q H) (comp-assoc r q K))
        base (binaryCong F ((H ◁ δ) ∙ comp-assoc r q H) ((K ◁ δ) ∙ comp-assoc r q K))
        (binaryCong F (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H)) (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)))
        (binary-pre-substitution F H K δ) (binary-pre-iterated F H K q r)
        (binary-combine F (H ◁ δ) (K ◁ δ) (comp-assoc r q H) (comp-assoc r q K) base)
        (binary-combine F a′ b′ ((H ◁ δ) ∙ comp-assoc r q H) ((K ◁ δ) ∙ comp-assoc r q K) base)

    long-normalization : long =₂
      (binaryCong F (c ∙ (a ▷ r)) (d ∙ (b ▷ r)) ∙ base)
    long-normalization =
      Paste.normalized-input-square R C
        (binaryCong F c d) (binaryPre F f x r) (binaryCong F a b ▷ r) (binaryPre F H K q ▷ r)
        (binaryCong F (a ▷ r) (b ▷ r)) (binaryPre F (H ∘ q) (K ∘ q) r)
        (normalization ▷ r) (binaryCong F (c ∙ (a ▷ r)) (d ∙ (b ▷ r)))
        (binary-pre-inputs F a b r)
        (preWhisker-isoComp-at (binaryCong F a b) (binaryPre F H K q) r)
        (binary-combine F c d (a ▷ r) (b ▷ r) base)

    assemble :
      (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H)) =₂ (c ∙ (a ▷ r))
      → (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) =₂ (d ∙ (b ▷ r))
      → short =₂ long
    assemble first second = long-normalization ⁻¹ ∙
      (isoComp-cong (binary-cong-Iso₂ F first second) (idIso base) ∙ short-normalization)
```
