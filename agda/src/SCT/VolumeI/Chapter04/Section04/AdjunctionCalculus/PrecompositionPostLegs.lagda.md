# The whiskered legs of the precomposition triangles

The literal left-unit and right-counit legs evaluate to the original
components, with the chosen common middle and outside frames.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionPostLegs
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S using (uncurry-expression)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionWhiskeredComponents as Whiskered
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionOuterFrame as Outer
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFramedOperations as Operations

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module W = Whiskered.At 𝒯 M ℱ P I E S adj K
  module N = W.N
  module B = W.B
  module LF = W.LF
  module RF = W.RF
  module LeftOuter = Outer.At 𝒯 M ℱ K r
  module RightOuter = Outer.At 𝒯 M ℱ K l
  module Left = Operations.At 𝒯 M ℱ P I E S (post-expression B.left B.unit)
    (W.RestrictedComponents.Left.source-frame ∙ W.p) (LF.evaluation-frame ∙ W.q) W.unit-evaluation
  module Right = Operations.At 𝒯 M ℱ P I E S (post-expression B.right B.counit)
    (RF.evaluation-frame ∙ W.p′) (W.RestrictedComponents.Right.target-frame ∙ W.q′) W.counit-evaluation

  abstract
    left-unit : ExpressionIso
      (retarget-expression (uncurry-expression B.Components.left-unit) LF.outside LF.middle) W.Triangles.Left.first
    left-unit = Left.retarget (comp-unitʳ B.left) ((comp-assoc B.left B.right B.left) ⁻¹) LF.outside LF.middle
      (LeftOuter.value ⁻¹)
      (isoComp-assoc-at LF.evaluation-frame (B.unit-target ▷ LF.W) (funPre-uncurry r (B.right ∘ B.left)) ∙ LF.post-comparison)

    right-counit : ExpressionIso
      (retarget-expression (uncurry-expression B.Components.right-counit) RF.middle RF.outside) W.Triangles.Right.second
    right-counit = Right.retarget ((comp-assoc B.right B.left B.right) ⁻¹) (comp-unitʳ B.right) RF.middle RF.outside
      (isoComp-assoc-at RF.evaluation-frame (B.counit-source ▷ RF.W) (funPre-uncurry l (B.left ∘ B.right)) ∙ RF.post-comparison)
      (RightOuter.value ⁻¹)
```
