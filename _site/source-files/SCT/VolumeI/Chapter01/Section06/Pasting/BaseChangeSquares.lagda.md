# Composing base-change squares

The outer rectangle of two pullback squares is again a pullback.
This is the existing pasting theorem, oriented for successive changes
of base in the definition of exponentiability.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)

module Successive {S T S′ T′ S″ T″ : CAT} (p : MAP S T) (b : MAP T′ T)
  (first : Cone p b S′) (b′ : MAP T″ T′) (second : Cone (Cone.right first) b′ S″) where

  composite : Cone p (b ∘ b′) S″
  composite = coneSwap (PasteCones.flatten b′ b (coneSwap first) (coneSwap second))

  abstract
    composite-isPullback : IsPullback first → IsPullback second → IsPullback composite
    composite-isPullback e₁ e₂ = pullback-swap _
      (Pasting.paste-isPullback b′ b p (coneSwap first) (pullback-swap first e₁)
        (coneSwap second) (pullback-swap second e₂))
```


Conversely, a specified pullback over the composite base map factors
through the first pullback. The resulting inner square is a pullback.
The displayed base map may be identified with the composite; the
factorization retains this identification in its entire cone comparison.

```agda
module Along {C D Z Q Γ A : CAT} (p : MAP C Z) (b : MAP D Z)
  (first : Cone p b Q) (first-isPullback : IsPullback first)
  (k : MAP Γ D) {a₀ : MAP Γ Z} (κ : (b ∘ k) =₁ a₀)
  (outer : Cone p a₀ A) (outer-isPullback : IsPullback outer) where
  private
    module Cancel = Cancellation.Framed 𝒯 P k b p κ
      (coneSwap first) (pullback-swap first first-isPullback)
      (coneSwap outer) (pullback-swap outer outer-isPullback)
      using (edge-cone; module WithComparison)
    module Target = UniversalCone (coneSwap first) (pullback-swap first first-isPullback)
      using (factor; factor-β)

  factor-cone : Cone b p A
  factor-cone = Cancel.edge-cone
  factor : MAP A Q
  factor = Target.factor factor-cone
  factor-computation : ConeIso (conePre factor (coneSwap first)) factor-cone
  factor-computation = Target.factor-β factor-cone

  module WithFactor (h : MAP A Q)
    (θ : ConeIso (conePre h (coneSwap first)) factor-cone) where
    private
      module Result = Cancel.WithComparison h θ using (square; square-isPullback)
    square : Cone (Cone.right first) k A
    square = record { left = h ; right = Cone.right outer ; match = ConeIso.leftIso θ }
    opaque
      square-isPullback : IsPullback square
      square-isPullback = pullback-cone-invariant
        (cone-match-change _ _ _ _ (inverse-inverse (ConeIso.leftIso θ)))
        (pullback-swap Result.square Result.square-isPullback)

  open WithFactor factor factor-computation public
```
