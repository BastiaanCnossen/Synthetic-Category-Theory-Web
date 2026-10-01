# Evaluated precomposition whiskerings

The whiskered curried unit and counit evaluate to the corresponding
original components. The displayed frames include the full object
restriction and the chosen normalization of each product coordinate.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionWhiskeredComponents
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S using (uncurry-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionRestrictedComponents as Restricted
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionEvaluatedTriangles as Evaluated
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingPrecompositionFrames as Pre

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module RestrictedComponents = Restricted.At 𝒯 M ℱ P I E S adj K
  module N = RestrictedComponents.N
  module B = N.B
  module LF = N.LeftFrames
  module RF = N.RightFrames
  module Triangles = Evaluated.At 𝒯 M ℱ P I E S adj K
  module Unit = Pre.At 𝒯 M ℱ P I E S B.unit N.unit-source B.unit-target N.unit-comparison
  module Counit = Pre.At 𝒯 M ℱ P I E S B.counit B.counit-source N.counit-target N.counit-comparison
  p : funUncurry (B.left ∘ id N.X) =₁ ((N.e ∘ pair pr₁ pr₂) ∘ LF.W)
  p = (N.unit-source ▷ LF.W) ∙ funPre-uncurry r (id N.X)
  q : funUncurry (B.left ∘ (B.right ∘ B.left)) =₁ ((N.e ∘ LF.H) ∘ LF.W)
  q = (B.unit-target ▷ LF.W) ∙ funPre-uncurry r (B.right ∘ B.left)
  p′ : funUncurry (B.right ∘ (B.left ∘ B.right)) =₁ ((N.d ∘ RF.H) ∘ RF.W)
  p′ = (B.counit-source ▷ RF.W) ∙ funPre-uncurry l (B.left ∘ B.right)
  q′ : funUncurry (B.right ∘ id N.Y) =₁ ((N.d ∘ pair pr₁ pr₂) ∘ RF.W)
  q′ = (N.counit-target ▷ RF.W) ∙ funPre-uncurry l (id N.Y)

  abstract
    unit-evaluation : ExpressionIso
      (retarget-expression (uncurry-expression (post-expression B.left B.unit))
        (RestrictedComponents.Left.source-frame ∙ p) (LF.evaluation-frame ∙ q)) Triangles.Left.first
    unit-evaluation = expressionIso-compose RestrictedComponents.Left.value
      (expressionIso-compose (retarget-expressionIso (Unit.value r)
          RestrictedComponents.Left.source-frame LF.evaluation-frame)
        (expressionIso-inverse (retarget-assoc (uncurry-expression (post-expression B.left B.unit)) p q
          RestrictedComponents.Left.source-frame LF.evaluation-frame)))

    counit-evaluation : ExpressionIso
      (retarget-expression (uncurry-expression (post-expression B.right B.counit))
        (RF.evaluation-frame ∙ p′) (RestrictedComponents.Right.target-frame ∙ q′)) Triangles.Right.second
    counit-evaluation = expressionIso-compose RestrictedComponents.Right.value
      (expressionIso-compose (retarget-expressionIso (Counit.value l)
          RF.evaluation-frame RestrictedComponents.Right.target-frame)
        (expressionIso-inverse (retarget-assoc (uncurry-expression (post-expression B.right B.counit)) p′ q′
          RF.evaluation-frame RestrictedComponents.Right.target-frame)))
```
