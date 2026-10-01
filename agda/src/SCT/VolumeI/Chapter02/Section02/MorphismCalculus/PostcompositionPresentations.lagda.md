# Functors preserve composite presentations

Apply the functor to the triangle family. The generic corner comparison
preserves its middle matching and both outer vertices. Segal uniqueness
then compares the resulting long edge with the chosen composite of the
two postcomposed expressions, including their prescribed endpoints.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationSubstitution as Original
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.PostcompositionCorners as Corners

module At {Γ C D : CAT} (F : MAP C D) {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z} {h : MorphismExpression x z}
  (p : CompositePresentation f g h) where
  module P₀ = CompositePresentation p
    using (short-edges; triangle)
  module Before = Original.Corners 𝒯 M ℱ P I E S p
    using (source-cone-comparison; target-cone-comparison)
  module First = MorphismExpression f
    using (arrow; source-frame; target-frame)
  module Second = MorphismExpression g
    using (arrow; source-frame; target-frame)
  module Long = MorphismExpression h
    using (arrow; source-frame; target-frame)
  triangle = funPost F ∘ P₀.triangle

  module Middle = Corners.FramedComparison 𝒯 M ℱ P I E F one zero d₂ d₀ (face-middle ⁻¹)
    P₀.triangle First.arrow Second.arrow First.target-frame Second.source-frame P₀.short-edges
  module Source = Corners.FramedComparison 𝒯 M ℱ P I E F zero zero d₁ d₂ face-bottom
    P₀.triangle Long.arrow First.arrow Long.source-frame First.source-frame Before.source-cone-comparison
  module Target = Corners.FramedComparison 𝒯 M ℱ P I E F one one d₁ d₀ (face-top ⁻¹)
    P₀.triangle Long.arrow Second.arrow Long.target-frame Second.target-frame Before.target-cone-comparison
  module V = Vertices (post-expression F f) (post-expression F g) (post-expression F h)
    triangle Middle.left-edge Middle.right-edge Source.left-edge
    using (MiddleVertex; SourceVertex; TargetVertex; presentation)

  middle-vertex : V.MiddleVertex
  middle-vertex = ConeIso.compatible Middle.comparison

  source-vertex : V.SourceVertex
  source-vertex = ConeIso.compatible Source.comparison

  target-vertex : V.TargetVertex
  target-vertex = ConeIso.compatible Target.comparison

  presentation : CompositePresentation (post-expression F f) (post-expression F g) (post-expression F h)
  presentation = V.presentation middle-vertex source-vertex target-vertex

post-presentation : {Γ C D : CAT} (F : MAP C D) {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z} {h : MorphismExpression x z} →
  CompositePresentation f g h →
  CompositePresentation (post-expression F f) (post-expression F g) (post-expression F h)
post-presentation = At.presentation

post-composition : {Γ C D : CAT} (F : MAP C D) {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) →
  ExpressionIso (compose-expression (post-expression F f) (post-expression F g))
    (post-expression F (compose-expression f g))
post-composition F f g = recognize-composite (post-presentation F (composition-presentation f g))

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.GlobalCompositionExpressions 𝒯 M ℱ P I E S
  using (global-compose-expression; global-composition-comparison)

global-post-composition : {Γ C D : CAT} (F : MAP C D) {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) →
  ExpressionIso (global-compose-expression (post-expression F f) (post-expression F g))
    (post-expression F (global-compose-expression f g))
global-post-composition F f g = expressionIso-compose
  (expressionIso-inverse (post-expressionIso F (global-composition-comparison f g)))
  (expressionIso-compose (post-composition F f g)
    (global-composition-comparison (post-expression F f) (post-expression F g)))
```
