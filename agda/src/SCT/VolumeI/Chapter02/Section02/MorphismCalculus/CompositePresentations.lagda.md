# Recognizing a composite by its triangle

A presentation specifies a triangle, its two short edges with their
middle matching, and an endpoint-preserving comparison of its long edge
with the proposed composite. The Segal axiom implies that two such
presentations give the same composite with its specified endpoints.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleComparisons 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I

presented-expression : {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z)
  (h : MAP Γ (Triangles C)) →
  ConeIso (conePre h (triangle-cone C)) (expression-pair f g) → MorphismExpression x z
presented-expression f g h β = retarget-expression
  (Presented.long-expression (expression-pair f g) h β)
  (MorphismExpression.source-frame f) (MorphismExpression.target-frame g)

record CompositePresentation {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z)
  (h : MorphismExpression x z) : Set m where
  field
    triangle : MAP Γ (Triangles C)
    short-edges : ConeIso (conePre triangle (triangle-cone C)) (expression-pair f g)
    long-edge : ExpressionIso (presented-expression f g triangle short-edges) h

composition-presentation : {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) →
  CompositePresentation f g (compose-expression f g)
composition-presentation f g = record
  { triangle = Complete.triangle (expression-pair f g)
  ; short-edges = Complete.short-edges (expression-pair f g)
  ; long-edge = expressionIso-id (compose-expression f g) }

composite-unique : {Γ C : CAT} {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z}
  {h k : MorphismExpression x z} →
  CompositePresentation f g h → CompositePresentation f g k → ExpressionIso h k
composite-unique {f = f} {g} p q = expressionIso-compose Q.long-edge
  (expressionIso-compose
    (retarget-expressionIso
      (Compare.long-comparison (expression-pair f g) P.triangle Q.triangle P.short-edges Q.short-edges)
      (MorphismExpression.source-frame f) (MorphismExpression.target-frame g))
    (expressionIso-inverse P.long-edge))
  where
  module P = CompositePresentation p
    using (long-edge; short-edges; triangle)
  module Q = CompositePresentation q
    using (long-edge; short-edges; triangle)

recognize-composite : {Γ C : CAT} {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z}
  {h : MorphismExpression x z} → CompositePresentation f g h →
  ExpressionIso (compose-expression f g) h
recognize-composite {f = f} {g} = composite-unique (composition-presentation f g)
```
