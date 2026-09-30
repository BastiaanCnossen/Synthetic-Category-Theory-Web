# Currying and invertibility of transformations

Uncurrying preserves and reflects the full inverse data of a framed
transformation. Reflection curries the two inverse expressions and
reflects their equations. No objectwise criterion or Rezk axiom is used.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.UncurryingInvertibility
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingReflection 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S using (IsInvertibleExpression; identified-invertible)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressions as Currying
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingCurryingRecovery as Recovery

module At {Γ X C : CAT} {f g : MAP Γ (Fun X C)} (α : MorphismExpression f g) where
  module Preserve (w : IsInvertibleExpression α) where
    module W = IsInvertibleExpression w
    abstract
      value : IsInvertibleExpression (uncurry-expression α)
      value = record
        { right-inverse = uncurry-expression W.right-inverse
        ; left-inverse = uncurry-expression W.left-inverse
        ; right-inverse-law = expressionIso-compose (uncurry-identity g)
            (expressionIso-compose (uncurry-cong W.right-inverse-law)
              (uncurry-composition W.right-inverse α))
        ; left-inverse-law = expressionIso-compose (uncurry-identity f)
            (expressionIso-compose (uncurry-cong W.left-inverse-law)
              (uncurry-composition α W.left-inverse)) }

  module Reflect (w : IsInvertibleExpression (uncurry-expression α)) where
    module W = IsInvertibleExpression w
    module Right = Currying.Curry 𝒯 M ℱ I g f W.right-inverse using (value)
    module Left = Currying.Curry 𝒯 M ℱ I g f W.left-inverse using (value)
    module RightRecovery = Recovery.At 𝒯 M ℱ P I E g f W.right-inverse using (value)
    module LeftRecovery = Recovery.At 𝒯 M ℱ P I E g f W.left-inverse using (value)
    abstract
      value : IsInvertibleExpression α
      value = record
        { right-inverse = Right.value
        ; left-inverse = Left.value
        ; right-inverse-law = uncurry-reflect
            (expressionIso-compose (expressionIso-inverse (uncurry-identity g))
              (expressionIso-compose W.right-inverse-law
                (expressionIso-compose (compose-expression-cong RightRecovery.value (expressionIso-id (uncurry-expression α)))
                  (expressionIso-inverse (uncurry-composition Right.value α)))))
        ; left-inverse-law = uncurry-reflect
            (expressionIso-compose (expressionIso-inverse (uncurry-identity f))
              (expressionIso-compose W.left-inverse-law
                (expressionIso-compose (compose-expression-cong (expressionIso-id (uncurry-expression α)) LeftRecovery.value)
                  (expressionIso-inverse (uncurry-composition α Left.value))))) }

module Curry {Γ X C : CAT} (f g : MAP Γ (Fun X C))
  (α : MorphismExpression (funUncurry f) (funUncurry g)) where
  module Curried = Currying.Curry 𝒯 M ℱ I f g α using (value)
  module Recover = Recovery.At 𝒯 M ℱ P I E f g α using (value)
  abstract
    value : IsInvertibleExpression α → IsInvertibleExpression Curried.value
    value w = At.Reflect.value Curried.value
      (identified-invertible (expressionIso-inverse Recover.value) w)
```
