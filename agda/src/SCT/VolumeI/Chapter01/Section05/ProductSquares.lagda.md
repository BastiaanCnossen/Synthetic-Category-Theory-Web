# Product projection squares

Changing one factor of a product gives a pullback square. Pasting with
the product square over the terminal category proves this directly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.ProductSquares
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section05.PullbackProducts 𝒯 P
  using (module TerminalBase; coneIso-over-One)
open import SCT.VolumeI.Chapter01.Section05.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯 using (coneSwap; coneSwap-swap)
open import SCT.VolumeI.Chapter01.Section05.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section05.PullbackEquivalences 𝒯 P using (degenerate-pullback)

module FirstFactor {C E : CAT} (f : MAP C E) (D : CAT) where

  square : Cone f (pr₁ {E} {D}) (C × D)
  square = record { left = pr₁ ; right = productMap f (id D)
    ; match = invIso (pair-β₁ (f ∘ pr₁) (id D ∘ pr₂)) }

  module Right = TerminalBase (terminate E) (terminate D)
  module Outer = TerminalBase (terminate E ∘ f) (terminate D)
  module Paste = Pasting f (terminate E) (terminate D) Right.productCone Right.productCone-isPullback

  square-isPullback : IsPullback square
  square-isPullback = Paste.cancel-isPullback square
    (pullback-cone-invariant (coneIso-over-One Outer.productCone (Paste.Paste.flatten square)
      (idIso pr₁) (invIso (comp-unitˡ pr₂ ∙ pair-β₂ (f ∘ pr₁) (id D ∘ pr₂))))
      Outer.productCone-isPullback)

module SecondFactor (E : CAT) {C D : CAT} (g : MAP C D) where

  square : Cone g (pr₂ {E} {D}) (E × C)
  square = record { left = pr₂ ; right = productMap (id E) g
    ; match = invIso (pair-β₂ (id E ∘ pr₁) (g ∘ pr₂)) }

  module Right = TerminalBase (terminate E) (terminate D)
  module Outer = TerminalBase (terminate E) (terminate D ∘ g)
  module Paste = Pasting g (terminate D) (terminate E) (coneSwap Right.productCone)
    (pullback-swap Right.productCone Right.productCone-isPullback)

  square-isPullback : IsPullback square
  square-isPullback = Paste.cancel-isPullback square
    (pullback-cone-invariant (coneIso-over-One (coneSwap Outer.productCone) (Paste.Paste.flatten square)
      (idIso pr₂) (invIso (comp-unitˡ pr₁ ∙ pair-β₁ (id E ∘ pr₁) (g ∘ pr₂))))
      (pullback-swap Outer.productCone Outer.productCone-isPullback))

module Graph {D E : CAT} (g : MAP D E) where

  graph = pair g (id D)
  diagonal = pair (id E) (id E)
  change = productMap (id E) g

  square : Cone change diagonal D
  square = record { left = graph ; right = g
    ; match = pair-iso (invIso m₁ ∙ n₁) (invIso m₂ ∙ n₂) }
    where
    n₁ = pair-β₁ g (id D) ∙
      (comp-unitˡ (pr₁ ∘ graph) ∙ (comp-assoc graph pr₁ (id E) ∙ project-pair₁ (id E ∘ pr₁) (g ∘ pr₂) graph))
    n₂ = comp-unitʳ g ∙ ((g ◁ pair-β₂ g (id D)) ∙
      (comp-assoc graph pr₂ g ∙ project-pair₂ (id E ∘ pr₁) (g ∘ pr₂) graph))
    m₁ = comp-unitˡ g ∙ project-pair₁ (id E) (id E) g
    m₂ = comp-unitˡ g ∙ project-pair₂ (id E) (id E) g

  module Bottom = SecondFactor E g
  module Paste = Pasting diagonal (pr₂ {E} {E}) g (coneSwap Bottom.square)
    (pullback-swap Bottom.square Bottom.square-isPullback)

  diagonal-projection-isEquiv : IsEquiv (pr₂ ∘ diagonal)
  diagonal-projection-isEquiv = equiv-transport (invIso (pair-β₂ (id E) (id E))) (id-isEquiv E)

  graph-projection-isEquiv : IsEquiv (pr₂ ∘ graph)
  graph-projection-isEquiv = equiv-transport (invIso (pair-β₂ g (id D))) (id-isEquiv D)

  square-isPullback : IsPullback square
  square-isPullback = pullback-cone-invariant (coneSwap-swap square)
    (pullback-swap (coneSwap square) (Paste.cancel-isPullback (coneSwap square)
      (pullback-cone-invariant (coneSwap-swap (Paste.Paste.flatten (coneSwap square)))
        (pullback-swap (coneSwap (Paste.Paste.flatten (coneSwap square)))
          (degenerate-pullback diagonal-projection-isEquiv (coneSwap (Paste.Paste.flatten (coneSwap square))) graph-projection-isEquiv)))))
```
