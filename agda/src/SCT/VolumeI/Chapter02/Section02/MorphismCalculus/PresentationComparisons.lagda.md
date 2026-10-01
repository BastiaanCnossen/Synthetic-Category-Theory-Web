# Changing the triangle or the proposed composite

A specified comparison of triangle families transports all three corner
comparisons. Changing the proposed long edge uses an endpoint-preserving
identification. Neither operation chooses another Segal lift.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationSubstitution as Original
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I using (expressionIso-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (ConeIso; coneIso-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)

change-long : {Γ C : CAT} {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z} {h k : MorphismExpression x z} →
  CompositePresentation f g h → ExpressionIso h k → CompositePresentation f g k
change-long p α = record
  { triangle = CompositePresentation.triangle p
  ; short-edges = CompositePresentation.short-edges p
  ; long-edge = expressionIso-compose α (CompositePresentation.long-edge p) }

module ChangeTriangle {Γ C : CAT} {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z} {h : MorphismExpression x z}
  (p : CompositePresentation f g h) {σ : MAP Γ (Triangles C)}
  (δ : σ =₁ CompositePresentation.triangle p) where
  module P₀ = CompositePresentation p
    using (short-edges)
  module Before = Original.Corners 𝒯 M ℱ P I E S p
    using (source-cone-comparison; target-cone-comparison)
  middle = coneIso-compose P₀.short-edges (cone-action (triangle-cone C) δ)
  source-corner = coneIso-compose Before.source-cone-comparison (cone-action (source-cone C) δ)
  target-corner = coneIso-compose Before.target-cone-comparison (cone-action (target-cone C) δ)
  module V = Vertices f g h σ (ConeIso.leftIso middle) (ConeIso.rightIso middle)
    (ConeIso.leftIso source-corner)
    using (MiddleVertex; SourceVertex; TargetVertex; presentation)

  middle-vertex : V.MiddleVertex
  middle-vertex = ConeIso.compatible middle
  source-vertex : V.SourceVertex
  source-vertex = ConeIso.compatible source-corner
  target-vertex : V.TargetVertex
  target-vertex = ConeIso.compatible target-corner

  presentation : CompositePresentation f g h
  presentation = V.presentation middle-vertex source-vertex target-vertex
```
