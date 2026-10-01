# Fixed-shape comparisons over an arbitrary base

This is an absolute pullback argument. The base category is arbitrary;
no theory of categories in that categorical context is used. A natural
comparison between the two diagram constructions, compatible with their
constant diagrams, gives a map of the defining cospans. Equivalences on
the three objects give an equivalence of the pullbacks, with its triangle
over the base.

The proof only needs the displayed data for the chosen functor to the
base. In applications they come from fixed-shape functor categories and
pullbacks, as in the manuscript.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as PullbackFunctor
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Equivalences
import SCT.VolumeI.Chapter01.Section06.Cones as Cones

module SCT.VolumeI.Chapter05.Section03.FixedShapeInheritance
  {l : Level} (S : Theory l l l) (P : Pullbacks.PullbackStructure S) where

open View S
open Pullbacks.PullbackStructure P
open PullbackFunctor S P using (CospanMap)
open Cones S using (ConeIso)
open Calculus S using (_then_)

module Comparison {Γ FX FΓ GX GΓ : CAT}
  (Fp : MAP FX FΓ) (Gp : MAP GX GΓ) (cF : MAP Γ FΓ) (cG : MAP Γ GΓ)
  (θX : Equiv FX GX) (θΓ : Equiv FΓ GΓ)
  (naturality : (Gp ∘ Equiv.functor θX) =₁ (Equiv.functor θΓ ∘ Fp))
  (constant : (Equiv.functor θΓ ∘ cF) =₁ cG) where

  cospan : CospanMap Fp cF Gp cG
  cospan = record
    { left = Equiv.functor θX ; right = id Γ ; base = Equiv.functor θΓ
    ; leftSquare = naturality ; rightSquare = comp-unitʳ cG then constant ⁻¹ }
  module Change = CospanMap cospan
  module E = Equivalences.CospanEquivalence S P cospan
    (Equiv.isEquiv θX) (id-isEquiv Γ) (Equiv.isEquiv θΓ) using (pullbackMap-isEquiv)

  comparison : MAP (Pullback Fp cF) (Pullback Gp cG)
  comparison = Change.pullbackMap

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = E.pullbackMap-isEquiv

  triangle : (pullback₂ {f = Gp} {g = cG} ∘ comparison) =₁ (pullback₂ {f = Fp} {g = cF})
  triangle = ConeIso.rightIso Change.pullbackMap-β then comp-unitˡ pullback₂

  equivalence : Equiv (Pullback Fp cF) (Pullback Gp cG)
  equivalence = record { functor = comparison ; isEquiv = comparison-isEquiv }
```
