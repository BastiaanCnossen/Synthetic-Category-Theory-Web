# Morphisms in a coslice give composition triangles

Reading a morphism between two arrows out of `x` gives a composition
triangle in the original category. Reconstructing its long edge in the
coslice recovers the target object, as a functor for every absolute
parameter category. All endpoint identifications are retained.

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

module SCT.VolumeI.Chapter04.Section03.CosliceTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (retarget-expressionIso)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceNaturality as Naturality
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Expressions
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Lifts

module At {Γ C : CAT} (x : Obj-abs C) {a b : MAP Γ (Coslice C x)}
  (u : MorphismExpression a b) where
  private
    module Read = Expressions.At 𝒯 M ℱ P I x using (universal; read; module Read; module FromExpression)
    module Triangle = Naturality.At 𝒯 M ℱ P I E S
      {Γ = Γ} {B = Coslice C x} {C = C} x {q = coslice-projection x}
      Read.universal {a = a} {b = b} u using (source-component; triangle)
    q = coslice-projection x

  composite : MorphismExpression (const x) (q ∘ b)
  composite = compose-expression Triangle.source-component (post-expression q u)

  open Triangle public using (triangle)

  private
    module Reconstructed = Read.FromExpression {Γ = Γ} b composite triangle
      using (comparison; comparison-image; left-image; right-image; specified-comparison)
  open Reconstructed public renaming
    (comparison to reconstruct-target; comparison-image to reconstruction-image;
     left-image to reconstruction-arrow; right-image to reconstruction-base)
```
