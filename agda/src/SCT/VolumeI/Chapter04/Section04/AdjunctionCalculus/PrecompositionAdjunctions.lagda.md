# Adjunctions induced by precomposition

For an adjunction with left adjoint l and right adjoint r, precomposition
by r is left adjoint to precomposition by l. The chosen component unit
and counit satisfy the literal triangle identities, reflected from the
original component triangles through common evaluation frames.

This proves the precomposition assertion of
`prop:Adjunction_On_Functor_Categories`.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionPostLegs as PostLegs
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionRestrictionLegs as RestrictionLegs
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingTriangleReflection as Reflection
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionEvaluatedTriangles as Triangles

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module Post = PostLegs.At 𝒯 M ℱ P I E S adj K using (module B; module LF; module RF; left-unit; right-counit)
  module Restrict = RestrictionLegs.At 𝒯 M ℱ P I E S adj K using (left-counit; right-unit)
  module B = Post.B using (left; right; unit; counit; module Components)
  module Target = Triangles.At 𝒯 M ℱ P I E S adj K using (left-triangle; right-triangle)
  module Left = Reflection.At 𝒯 M ℱ P I E S {Γ = Fun C K} {X = D} {C = K}
    {f = B.left} {g = (B.left ∘ B.right) ∘ B.left}
    B.Components.left-unit B.Components.left-counit
    {h = Post.LF.outside-object} {k = Post.LF.middle-object} Post.LF.outside Post.LF.middle using (reflect)
  module Right = Reflection.At 𝒯 M ℱ P I E S {Γ = Fun D K} {X = C} {C = K}
    {f = B.right} {g = (B.right ∘ B.left) ∘ B.right}
    B.Components.right-unit B.Components.right-counit
    {h = Post.RF.outside-object} {k = Post.RF.middle-object} Post.RF.outside Post.RF.middle using (reflect)

  abstract
    value : Adjunction (funPre {D = K} r) (funPre {D = K} l)
    value = record
      { unit = B.unit
      ; counit = B.counit
      ; left-triangle = Left.reflect (expressionIso-compose Target.left-triangle
          (compose-expression-cong Post.left-unit Restrict.left-counit))
      ; right-triangle = Right.reflect (expressionIso-compose Target.right-triangle
          (compose-expression-cong Restrict.right-unit Post.right-counit)) }
```
