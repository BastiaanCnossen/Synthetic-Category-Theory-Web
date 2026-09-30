# Pullback squares from a specified map on fibers

A comparison between the inclusions of two fibers gives a pullback
square when its projected matching is the specified comparison over the
base. This packages pullback cancellation without discarding that
higher compatibility equation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Pasting.FiberSquares
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation

module Along {A B C D X Y : CAT} (f : MAP A B) (p : MAP B C) (q : MAP A C)
  (κ : (p ∘ f) =₁ q) (z : MAP D C)
  (target : Cone p z X) (target-isPullback : IsPullback target)
  (source : Cone q z Y) (source-isPullback : IsPullback source)
  (h : MAP Y X) (θ : (f ∘ Cone.left source) =₁ (Cone.left target ∘ h))
  (μ : (Cone.right target ∘ h) =₁ Cone.right source) where
  private
    module Cancel = Cancellation.Framed 𝒯 P f p z κ
      target target-isPullback source source-isPullback using (edge-cone; module WithComparison)
    E = Cone.match Cancel.edge-cone
    T = Cone.match (conePre h target)
    R = z ◁ μ
    L = p ◁ θ

  projection-equation : Set m
  projection-equation = ((R ∙ T) ∙ L) =₂ E

  square : Cone f (Cone.left target) Y
  square = record { left = Cone.left source ; right = h ; match = θ }

  module Compatible (w : projection-equation) where
    private
      comparison : ConeIso (conePre h target) Cancel.edge-cone
      comparison = record { leftIso = θ ⁻¹ ; rightIso = μ
        ; compatible = cancel-right L (R ∙ T) ∙
            isoComp-cong (w ⁻¹) (post-inverse p θ) }
      module Result = Cancel.WithComparison h comparison using (square; square-isPullback)
    abstract
      square-isPullback : IsPullback square
      square-isPullback = pullback-cone-invariant
        (cone-match-change (Cone.left source) h _ _ (inverse-inverse θ)) Result.square-isPullback
```
