# Substituting in a composite presentation

A composite presentation can be restricted to new parameters and have
its three object frames retargeted. The three vertex equations travel
with it. This operation restricts a given triangle and does not choose
a new Segal lift.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.FramedConeRestriction as Framed
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.TransposedEndpointFrames as Frames
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open Frames.FrameCalculus 𝒯 M ℱ P using (quotient-common)

module Corners {Γ C : CAT} {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z} {h : MorphismExpression x z}
  (p : CompositePresentation f g h) where
  module P₀ = CompositePresentation p
    using (long-edge; short-edges; triangle)
  module F = MorphismExpression f
  module G = MorphismExpression g
    using (arrow; source-frame; target-frame)
  module H = MorphismExpression h
  module Long = ExpressionIso P₀.long-edge
    using (comparison; source-compatible; target-compatible)
  module V = Vertices f g h P₀.triangle
    (ConeIso.leftIso P₀.short-edges) (ConeIso.rightIso P₀.short-edges) Long.comparison
    using (MiddleVertex; SourceVertex; TargetVertex; presentation)

  middle : V.MiddleVertex
  middle = ConeIso.compatible P₀.short-edges

  abstract
    source-vertex : V.SourceVertex
    source-vertex = cancel-left F.source-frame _ ∙
      (isoComp-cong (idIso (F.source-frame ⁻¹)) Long.source-compatible ∙
        isoComp-assoc-at (F.source-frame ⁻¹) H.source-frame (ev₀ ◁ Long.comparison))

    target-vertex : V.TargetVertex
    target-vertex = cancel-left G.target-frame _ ∙
      (isoComp-cong (idIso (G.target-frame ⁻¹)) Long.target-compatible ∙
        isoComp-assoc-at (G.target-frame ⁻¹) H.target-frame (ev₁ ◁ Long.comparison))

  source-cone-comparison : ConeIso (conePre P₀.triangle (source-cone C))
    (Framed.framed-cone 𝒯 M ℱ P H.arrow F.arrow H.source-frame F.source-frame)
  source-cone-comparison = record
    { leftIso = Long.comparison ; rightIso = ConeIso.leftIso P₀.short-edges ; compatible = source-vertex }

  target-cone-comparison : ConeIso (conePre P₀.triangle (target-cone C))
    (Framed.framed-cone 𝒯 M ℱ P H.arrow G.arrow H.target-frame G.target-frame)
  target-cone-comparison = record
    { leftIso = Long.comparison ; rightIso = ConeIso.rightIso P₀.short-edges ; compatible = target-vertex }

module Restrict {Γ Δ C : CAT} {x y z : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z} {h : MorphismExpression x z}
  (p : CompositePresentation f g h) (r : MAP Δ Γ) where
  module K = Corners p
  module P₀ = CompositePresentation p
    using (long-edge; short-edges; triangle)
  module F = MorphismExpression f
  module G = MorphismExpression g
    using (arrow; source-frame; target-frame)
  module H = MorphismExpression h
  module Middle = Framed.RestrictComparison 𝒯 M ℱ P (triangle-cone C) P₀.triangle r
    F.arrow G.arrow F.target-frame G.source-frame P₀.short-edges
  module Source = Framed.RestrictComparison 𝒯 M ℱ P (source-cone C) P₀.triangle r
    H.arrow F.arrow H.source-frame F.source-frame K.source-cone-comparison
  module Target = Framed.RestrictComparison 𝒯 M ℱ P (target-cone C) P₀.triangle r
    H.arrow G.arrow H.target-frame G.target-frame K.target-cone-comparison
  module V = Vertices (restrict-expression f r) (restrict-expression g r) (restrict-expression h r)
    (P₀.triangle ∘ r) Middle.left-edge Middle.right-edge Source.left-edge
    using (MiddleVertex; SourceVertex; TargetVertex; presentation)

  middle-vertex : V.MiddleVertex
  middle-vertex = ConeIso.compatible Middle.comparison
  source-vertex : V.SourceVertex
  source-vertex = ConeIso.compatible Source.comparison
  target-vertex : V.TargetVertex
  target-vertex = ConeIso.compatible Target.comparison

  value : CompositePresentation (restrict-expression f r) (restrict-expression g r) (restrict-expression h r)
  value = V.presentation middle-vertex source-vertex target-vertex

module Retarget {Γ C : CAT} {x y z x′ y′ z′ : MAP Γ C}
  {f : MorphismExpression x y} {g : MorphismExpression y z} {h : MorphismExpression x z}
  (p : CompositePresentation f g h) (α : x =₁ x′) (β : y =₁ y′) (γ : z =₁ z′) where
  module K = Corners p
  module P₀ = CompositePresentation p
    using (long-edge; short-edges; triangle)
  module F = MorphismExpression f
  module G = MorphismExpression g
    using (arrow; source-frame; target-frame)
  module H = MorphismExpression h
  module V = Vertices (retarget-expression f α β) (retarget-expression g β γ)
    (retarget-expression h α γ) P₀.triangle
    (ConeIso.leftIso P₀.short-edges) (ConeIso.rightIso P₀.short-edges)
    (ExpressionIso.comparison P₀.long-edge)
    using (MiddleVertex; SourceVertex; TargetVertex; presentation)

  middle-vertex : V.MiddleVertex
  middle-vertex = K.middle ∙ isoComp-cong (quotient-common F.target-frame G.source-frame β)
    (idIso (ev₁ ◁ ConeIso.leftIso P₀.short-edges))
  source-vertex : V.SourceVertex
  source-vertex = K.source-vertex ∙ isoComp-cong (quotient-common H.source-frame F.source-frame α)
    (idIso (ev₀ ◁ ExpressionIso.comparison P₀.long-edge))
  target-vertex : V.TargetVertex
  target-vertex = K.target-vertex ∙ isoComp-cong (quotient-common H.target-frame G.target-frame γ)
    (idIso (ev₁ ◁ ExpressionIso.comparison P₀.long-edge))

  value : CompositePresentation (retarget-expression f α β) (retarget-expression g β γ)
    (retarget-expression h α γ)
  value = V.presentation middle-vertex source-vertex target-vertex
```
