# Evaluating the parameter-restricted adjunction components

The restricted counit and unit evaluate to the other two legs of the
precomposition triangles. Their middle frames are the chosen separation
frames, and their outside frames retain identity evaluation.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionParameterEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PairedComponentParameters as Parameters
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionEvaluatedTriangles as Triangles
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PairedCoordinatePostcomposition as Coordinate
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedParameterChange as Evaluation
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionMiddleRestriction as Middle
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionRestrictedOuterFrame as Outer

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module A = Adjunction adj using (unit-at; counit-at)
  X = Fun C K
  Y = Fun D K
  L : MAP X Y
  L = funPre r
  R : MAP Y X
  R = funPre l
  e : MAP (X × C) K
  e = funEval
  d : MAP (Y × D) K
  d = funEval
  module Target = Triangles.At 𝒯 M ℱ P I E S adj K
  module Paired = Parameters.At 𝒯 M ℱ P I E S adj using (module Unit; module Counit)
  module LeftPair = Paired.Counit L using (σ; value; module Pair; module Middle; module Outside)
  module RightPair = Paired.Unit R using (σ; value; module Pair; module Middle; module Outside)
  module LeftCoordinate = Coordinate.At 𝒯 M ℱ P I E S r (A.counit-at (pr₂ {X} {D})) using (result; source-frame; target-frame; value)
  module RightCoordinate = Coordinate.At 𝒯 M ℱ P I E S l (A.unit-at (pr₂ {Y} {C})) using (result; source-frame; target-frame; value)
  module LeftMiddle = Middle.At 𝒯 M ℱ P K l r
  module RightMiddle = Middle.At 𝒯 M ℱ P K r l
  module LeftOuter = Outer.At 𝒯 M ℱ K r
  module RightOuter = Outer.At 𝒯 M ℱ K l
  module Left = Evaluation.At 𝒯 M ℱ P I E S LeftPair.σ (productMap (id X) r) d e (funPre-β r)
    LeftPair.Pair.γY LeftPair.Pair.γX LeftCoordinate.result
    LeftPair.Middle.Changed.ν LeftPair.Outside.Changed.ν
    LeftCoordinate.source-frame LeftCoordinate.target-frame LeftPair.value LeftCoordinate.value using (value; original)
  module Right = Evaluation.At 𝒯 M ℱ P I E S RightPair.σ (productMap (id Y) l) e d (funPre-β l)
    RightPair.Pair.γY RightPair.Pair.γX RightCoordinate.result
    RightPair.Outside.Changed.ν RightPair.Middle.Changed.ν
    RightCoordinate.source-frame RightCoordinate.target-frame RightPair.value RightCoordinate.value using (value; original)

  abstract
    left-counit : ExpressionIso
      (retarget-expression (restrict-expression (post-expression d LeftPair.Pair.γY) LeftPair.σ)
        LeftMiddle.SeparationResult.Ξ LeftOuter.Ω) Target.Left.second
    left-counit = expressionIso-compose Left.value
      (retarget-cong Left.original (idIso LeftMiddle.SeparationResult.Ξ) (LeftOuter.value ⁻¹))

    right-unit : ExpressionIso
      (retarget-expression (restrict-expression (post-expression e RightPair.Pair.γY) RightPair.σ)
        RightOuter.Ω RightMiddle.SeparationResult.Ξ) Target.Right.first
    right-unit = expressionIso-compose Right.value
      (retarget-cong Right.original (RightOuter.value ⁻¹) (idIso RightMiddle.SeparationResult.Ξ))
```
