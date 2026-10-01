# The iterated-coslice projection is precomposition

Flattening an iterated coslice is compatible with its projection to the
original coslice. The comparison follows by applying naturality to the
universal arrow of that original coslice: the long edge of the resulting
composition triangle reconstructs the projected object.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section03.IteratedCoslicePrecomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)
import SCT.VolumeI.Chapter04.Section03.IteratedCoslices as Iterated
import SCT.VolumeI.Chapter04.Section03.CosliceTriangles as Triangles
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Expressions
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageExpressions as Images
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceObjectPrecomposition as Precomposition
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifts
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (ConeIso; conePre; coneIso-compose)
open Laws.PullbackStructure P using (pullbackCone)

module At {C : CAT} (x : Obj-abs C) (u : Obj-abs (Coslice C x)) where
  private
    q = coslice-projection x
    y = q ∘ u
    T = Coslice (Coslice C x) u
    π = coslice-projection u
    module Flatten = Iterated.At 𝒯 M ℱ P I E S Q x u using (functor; isEquiv)
    module Pre = Precomposition.At 𝒯 M ℱ P I E S x u using (functor; family; module Restricted)
    module ReadX = Expressions.At 𝒯 M ℱ P I x using (read)
    module ReadY = Expressions.At 𝒯 M ℱ P I y using (read)
    module ReadU = Expressions.At 𝒯 M ℱ P I u using (universal)
    module Image = Images.Image 𝒯 M ℱ P I q u using (expression-computation; projection)
    module Triangle = Triangles.At 𝒯 M ℱ P I E S {Γ = T} {C = C} x
      {a = const {P = T} u} {b = π} ReadU.universal using (reconstruct-target; specified-comparison)
    module Lift = Lifts.At 𝒯 M ℱ P I x using (module Change)
    f = Pre.family T
    g = ReadY.read {Γ = T} Flatten.functor
    a₀ = ReadX.read {Γ = T} (const {P = T} u)
    b₀ = post-expression q ReadU.universal
    γ = constant-image T q u
    ε = Image.projection
    source-id = idIso (const {P = T} x)
    middle-id = idIso (const {P = T} y)
    target-id = idIso (q ∘ π)
    left-expression = compose-expression {Γ = T} f g
    triangle-expression = compose-expression {Γ = T} a₀ b₀

    abstract
      expression-comparison : ExpressionIso (retarget-expression left-expression source-id ε) triangle-expression
      expression-comparison = expressionIso-compose (retarget-id triangle-expression)
        (expressionIso-compose (retarget-composition a₀ b₀ source-id γ target-id)
        (expressionIso-compose (compose-expression-cong (retarget-id f) Image.expression-computation)
          (expressionIso-inverse (retarget-composition f g source-id middle-id ε))))

  functor = Flatten.functor
  precompose = Pre.functor
  isEquiv = Flatten.isEquiv

  private
    module Changed = Lift.Change {Γ = T} {b = coslice-projection y ∘ functor} {d = q ∘ π}
      left-expression triangle-expression ε expression-comparison
      using (specified-comparison)
  projection-computation : ConeIso
    (conePre (precompose ∘ functor) (pullbackCone endpoints (pair (const x) (id C))))
    (conePre π (pullbackCone endpoints (pair (const x) (id C))))
  projection-computation = coneIso-compose Triangle.specified-comparison
    (coneIso-compose Changed.specified-comparison (Pre.Restricted.specified-comparison functor))
  private
    module Reflected = Reflection.Lift 𝒯 P (precompose ∘ functor) π projection-computation
      using (lift; comparison-image; left-image; right-image)
  open Reflected public renaming
    (lift to projection; comparison-image to projection-image;
     left-image to projection-arrow; right-image to projection-target)

  over-coslice : FunctorOver π precompose
  over-coslice = record { lift = functor ; comparison = projection }
```
