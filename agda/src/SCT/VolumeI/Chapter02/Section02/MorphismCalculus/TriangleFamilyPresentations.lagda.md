# A triangle family presents its composite

The transposed middle, source, and target corners now use the chosen
Segal triangle cones. The conversion changes no edge comparison. Thus an
absolute triangle witness in `Fun Γ C` gives a composite presentation on
`Γ`, with separate proofs for both endpoints of its long edge.

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
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedTriangleFamilies as Evaluated
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointCornerFamilies as Corners

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleFamilyPresentations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleFamilies 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices 𝒯 M ℱ P I E S
  using (module Vertices; CompositePresentation; compose-expression)

module Witness {Γ C : CAT} {x y z : Obj-abs (Fun Γ C)}
  {f : Morphism x y} {g : Morphism y z} {h : Morphism x z}
  (w : CompositeWitness f g h) where
  module Family = Evaluated.Family.Witness 𝒯 M ℱ P I E w
    using (first-edge; long-edge; middle-vertex; second-edge; source-vertex; target-vertex)
  module T = TransposedWitness w
    using (triangle)
  module First = Evaluated.Family.Arrow 𝒯 M ℱ P I E f
    using (as-expression)
  module Second = Evaluated.Family.Arrow 𝒯 M ℱ P I E g
    using (as-expression)
  module Long = Evaluated.Family.Arrow 𝒯 M ℱ P I E h
    using (as-expression)
  module Middle = Corners.At 𝒯 M ℱ P middle-square T.triangle
    using (matching)
  module Source = Corners.At 𝒯 M ℱ P source-square T.triangle
    using (matching)
  module Target = Corners.At 𝒯 M ℱ P target-square T.triangle
    using (reversed-matching)
  module V = Vertices First.as-expression Second.as-expression Long.as-expression
    T.triangle Family.first-edge Family.second-edge Family.long-edge
    using (MiddleVertex; SourceVertex; TargetVertex; composite-comparison; presentation)

  abstract
    middle-vertex : V.MiddleVertex
    middle-vertex = isoComp-cong (idIso (ev₀ ◁ Family.second-edge)) Middle.matching ∙
      Family.middle-vertex

    source-vertex : V.SourceVertex
    source-vertex = isoComp-cong (idIso (ev₀ ◁ Family.first-edge)) Source.matching ∙
      Family.source-vertex

    target-vertex : V.TargetVertex
    target-vertex = isoComp-cong (idIso (ev₁ ◁ Family.second-edge)) Target.reversed-matching ∙
      Family.target-vertex

  presentation : CompositePresentation First.as-expression Second.as-expression Long.as-expression
  presentation = V.presentation middle-vertex source-vertex target-vertex

  composite-comparison :
    ExpressionIso (compose-expression First.as-expression Second.as-expression) Long.as-expression
  composite-comparison = V.composite-comparison middle-vertex source-vertex target-vertex
```
