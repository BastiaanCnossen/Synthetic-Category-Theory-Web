# The restricted legs of the precomposition triangles

The literal left-counit and right-unit legs use the same middle and
outside frames as the whiskered legs. This completes the endpoint
comparisons needed to reflect both evaluated triangles.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionRestrictionLegs
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S using (uncurry-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionParameterEvaluation as Evaluation
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionCompositeMiddle as Middle
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFramedOperations as Operations

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module MiddleFrames = Middle.At 𝒯 M ℱ P I E S adj K
  module N = MiddleFrames.N
  module B = N.B
  module LF = N.LeftFrames
  module RF = N.RightFrames
  module Evaluated = Evaluation.At 𝒯 M ℱ P I E S adj K
  module LeftOuter = Evaluated.LeftOuter
  module RightOuter = Evaluated.RightOuter
  module LeftMiddle = Evaluated.LeftMiddle
  module RightMiddle = Evaluated.RightMiddle
  module Counit = Operations.At 𝒯 M ℱ P I E S B.counit B.counit-source N.counit-target N.counit-comparison using (restrict)
  module Unit = Operations.At 𝒯 M ℱ P I E S B.unit N.unit-source B.unit-target N.unit-comparison using (restrict)
  p = (B.counit-source ▷ LeftMiddle.σ) ∙ funUncurry-restrict (B.left ∘ B.right) B.left
  q = (N.counit-target ▷ LeftMiddle.σ) ∙ funUncurry-restrict (id N.Y) B.left
  p′ = (N.unit-source ▷ RightMiddle.σ) ∙ funUncurry-restrict (id N.X) B.right
  q′ = (B.unit-target ▷ RightMiddle.σ) ∙ funUncurry-restrict (B.right ∘ B.left) B.right

  abstract
    left-evaluated : ExpressionIso
      (retarget-expression (uncurry-expression (restrict-expression B.counit B.left))
        (LeftMiddle.SeparationResult.Ξ ∙ p) (LeftOuter.Ω ∙ q)) Evaluated.Target.Left.second
    left-evaluated = expressionIso-compose Evaluated.left-counit
      (expressionIso-compose (retarget-expressionIso (Counit.restrict B.left) LeftMiddle.SeparationResult.Ξ LeftOuter.Ω)
        (expressionIso-inverse (retarget-assoc (uncurry-expression (restrict-expression B.counit B.left))
          p q LeftMiddle.SeparationResult.Ξ LeftOuter.Ω)))

    right-evaluated : ExpressionIso
      (retarget-expression (uncurry-expression (restrict-expression B.unit B.right))
        (RightOuter.Ω ∙ p′) (RightMiddle.SeparationResult.Ξ ∙ q′)) Evaluated.Target.Right.first
    right-evaluated = expressionIso-compose Evaluated.right-unit
      (expressionIso-compose (retarget-expressionIso (Unit.restrict B.right) RightOuter.Ω RightMiddle.SeparationResult.Ξ)
        (expressionIso-inverse (retarget-assoc (uncurry-expression (restrict-expression B.unit B.right))
          p′ q′ RightOuter.Ω RightMiddle.SeparationResult.Ξ)))

  module Left = Operations.At 𝒯 M ℱ P I E S (restrict-expression B.counit B.left)
    (LeftMiddle.SeparationResult.Ξ ∙ p) (LeftOuter.Ω ∙ q) left-evaluated using (retarget)
  module Right = Operations.At 𝒯 M ℱ P I E S (restrict-expression B.unit B.right)
    (RightOuter.Ω ∙ p′) (RightMiddle.SeparationResult.Ξ ∙ q′) right-evaluated using (retarget)

  abstract
    left-counit : ExpressionIso
      (retarget-expression (uncurry-expression B.Components.left-counit) LF.middle LF.outside) Evaluated.Target.Left.second
    left-counit = Left.retarget (idIso ((B.left ∘ B.right) ∘ B.left)) (comp-unitˡ B.left) LF.middle LF.outside
      (MiddleFrames.left-restricted-middle ∙ isoComp-unitʳ-at LF.middle ∙
        isoComp-cong (idIso LF.middle) (funUncurryIso-id ((B.left ∘ B.right) ∘ B.left)))
      (LeftOuter.unit-value ⁻¹)

    right-unit : ExpressionIso
      (retarget-expression (uncurry-expression B.Components.right-unit) RF.outside RF.middle) Evaluated.Target.Right.first
    right-unit = Right.retarget (comp-unitˡ B.right) (idIso ((B.right ∘ B.left) ∘ B.right)) RF.outside RF.middle
      (RightOuter.unit-value ⁻¹)
      (MiddleFrames.right-restricted-middle ∙ isoComp-unitʳ-at RF.middle ∙
        isoComp-cong (idIso RF.middle) (funUncurryIso-id ((B.right ∘ B.left) ∘ B.right)))
```
