# Pulling back transformations with specified endpoints

A transformation between the projected relative functors lifts to a
transformation over the pullback base. Relative endpoint identifications
supply the whole endpoint cones. The left projection recovers the given
transformation after those endpoint identifications, with its actual
frames retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.RelativeCategories.PullbackMorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P using (postbase)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse; retarget-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications 𝒯 M ℱ P I E
  using (retarget-curried)
import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.RelativeIntervalCones as Intervals
import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackRelativeComparisons as Comparisons
import SCT.VolumeI.Chapter03.RelativeCategories.PullbackMorphismLifting as Lifting
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismDiagramRecovery as Recovery

module At {C D B T Γ : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) (et : IsPullback t) (q : MAP Γ D)
  (u v : FunctorOver q (Cone.right t)) where
  U : FunctorOver (g ∘ Cone.right t) f
  U = record { lift = Cone.left t ; comparison = Cone.match t }
  module Source = Comparisons.At 𝒯 M ℱ P t q u using (module WithComparison)
  module Target = Comparisons.At 𝒯 M ℱ P t q v using (module WithComparison)

  module Given {x y : FunctorOver (g ∘ q) f}
    (α : Over.MorphismOver (g ∘ q) f x y)
    (ξ : FunctorOverIso x (compose-over U (postbase g u)))
    (ζ : FunctorOverIso y (compose-over U (postbase g v))) where
    module Diagram = Intervals.At 𝒯 M ℱ P I E S f g q α
      using (H; value; module Source; module Target)
    module Recover = Recovery.Roundtrip 𝒯 M ℱ P I E S α
      using (underlying-comparison)
    source-cone = coneIso-compose (Source.WithComparison.value x ξ) Diagram.Source.comparison
    target-cone = coneIso-compose (Target.WithComparison.value y ζ) Diagram.Target.comparison
    source-right : (FunctorLift.comparison u ∙ ConeIso.rightIso source-cone) =₂ identity-boundary zero q
    source-right = cancel-inverse (FunctorLift.comparison u) (identity-boundary zero q)
    target-right : (FunctorLift.comparison v ∙ ConeIso.rightIso target-cone) =₂ identity-boundary one q
    target-right = cancel-inverse (FunctorLift.comparison v) (identity-boundary one q)
    module Lift = Lifting.At.WithEndpoints 𝒯 M ℱ P I E S t et q Diagram.H (Cone.match Diagram.value)
      u v source-cone target-cone source-right target-right using (underlying; value; left-image)

    value : Over.MorphismOver q (Cone.right t) u v
    value = Lift.value
    underlying : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v)
    underlying = Lift.underlying
    source-frame = FunctorOverIso.underlying ξ
    target-frame = FunctorOverIso.underlying ζ
    projected = retarget-expression (Over.MorphismOver.underlying α) source-frame target-frame

    abstract
      left-image : ExpressionIso (post-expression (Cone.left t) underlying) projected
      left-image = expressionIso-compose
        (expressionIso-inverse
          (expressionIso-compose
            (retarget-curried Diagram.H
              (ConeIso.leftIso Diagram.Source.comparison) (ConeIso.leftIso Diagram.Target.comparison)
              source-frame target-frame)
            (retarget-expressionIso Recover.underlying-comparison source-frame target-frame)))
        Lift.left-image
```
