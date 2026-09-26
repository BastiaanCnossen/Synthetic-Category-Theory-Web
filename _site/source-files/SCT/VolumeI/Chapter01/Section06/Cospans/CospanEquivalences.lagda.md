# Equivalences of cospans

For `exercise:Fiber_Product_Of_Equivalences_Is_Equivalence`, paste the
source pullback with the right square of the cospan map. The specified
factorization comparison identifies this rectangle with the rectangle
through the target pullback. Pasting cancellation finishes the proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullbackCone-isPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanCartesian 𝒯 P public using (prefix-assoc)
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanCartesian as Cartesian

module CospanEquivalence {C D E C′ D′ E′ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (eu : IsEquiv (CospanMap.left F))
  (ev : IsEquiv (CospanMap.right F)) (ew : IsEquiv (CospanMap.base F)) where

  open Cartesian.CospanCartesian 𝒯 P F eu
    (degenerate-pullback ew (Cartesian.rightSquareOf 𝒯 P F) ev) public hiding (pullbackMap-isEquiv)

  pullbackMap-isEquiv : IsEquiv (CospanMap.pullbackMap F)
  pullbackMap-isEquiv = Cartesian.CospanCartesian.pullbackMap-isEquiv 𝒯 P F eu
    (degenerate-pullback ew (Cartesian.rightSquareOf 𝒯 P F) ev)
```
