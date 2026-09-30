# Pullbacks between successive factorizations

Two successive applications of pullback cancellation compare the
factorizations through the pullbacks of g and gf. A further functor
into the first pullback need only have a specified projection
comparison. The resulting square retains that comparison in its
matching. This is the pullback part of the composition law for
directed evaluation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Pasting.FactoredComposition
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation

module At {A B C Z Y X : CAT} (f : MAP A B) (g : MAP B C) (k : MAP Z C)
  (s : Cone g k Y) (es : IsPullback s)
  (t : Cone (g ∘ f) k X) (et : IsPullback t) where
  module Target = UniversalCone s es using (factor; factor-β)
  h : MAP X Y
  h = Target.factor (compositeCone f g t)
  h-comparison : ConeIso (conePre h s) (compositeCone f g t)
  h-comparison = Target.factor-β (compositeCone f g t)
  module Outer = Cancellation.At 𝒯 P f g k s es t et h h-comparison
    using (square; square-isPullback)

  outer-square : Cone (Cone.left s) f X
  outer-square = coneSwap Outer.square
  outer-isPullback : IsPullback outer-square
  outer-isPullback = pullback-swap Outer.square Outer.square-isPullback

  module Factor {W V : CAT} (r : MAP W Y) (b : MAP W B)
    (κ : (Cone.left s ∘ r) =₁ b)
    (q : Cone b f V) (eq : IsPullback q) where
    module Cancel = Cancellation.Framed 𝒯 P r (Cone.left s) f κ
      outer-square outer-isPullback q eq using (edge-cone; module WithComparison)
    module Lift = UniversalCone outer-square outer-isPullback using (factor; factor-β)
    map : MAP V X
    map = Lift.factor Cancel.edge-cone
    map-comparison : ConeIso (conePre map outer-square) Cancel.edge-cone
    map-comparison = Lift.factor-β Cancel.edge-cone
    module Result = Cancel.WithComparison map map-comparison using (square; square-isPullback)
    open Result public
```
