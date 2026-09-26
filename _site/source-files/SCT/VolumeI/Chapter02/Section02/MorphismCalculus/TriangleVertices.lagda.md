# The three vertex equations of a composite

The middle vertex makes the two short-edge comparisons a comparison of
whole cones. The source and target vertices then say that the long-edge
comparison preserves its specified endpoints. Keeping these as three
separate statements makes each obligation visible before Segal uniqueness
is used.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

-- Cancel a specified endpoint frame after comparing the corner.
vertex-from-corner : {Γ C : CAT} {u v w z : MAP Γ C}
  (p : v =₁ z) (q : w =₁ z) (l : u =₁ w) (r : u =₁ v) →
  ((p ⁻¹ ∙ q) ∙ l) =₂ r → (q ∙ l) =₂ (p ∙ r)
vertex-from-corner p q l r corner =
  (isoComp-cong (idIso p) corner) ∙
  (isoComp-assoc-at p (p ⁻¹ ∙ q) l ∙
    isoComp-cong ((cancel-inverse p q) ⁻¹) (idIso l))

module Vertices {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z)
  (h : MorphismExpression x z) (σ : MAP Γ (Triangles C))
  (first-edge : (edge₂ ∘ σ) =₁ MorphismExpression.arrow f)
  (second-edge : (edge₀ ∘ σ) =₁ MorphismExpression.arrow g)
  (long-edge : (edge₁ ∘ σ) =₁ MorphismExpression.arrow h) where
  module F = MorphismExpression f
  module G = MorphismExpression g
  module H = MorphismExpression h

  MiddleVertex : Set m
  MiddleVertex = ((G.source-frame ⁻¹ ∙ F.target-frame) ∙ (ev₁ ◁ first-edge)) =₂
    ((ev₀ ◁ second-edge) ∙ Cone.match (conePre σ (triangle-cone C)))

  SourceVertex : Set m
  SourceVertex = ((F.source-frame ⁻¹ ∙ H.source-frame) ∙ (ev₀ ◁ long-edge)) =₂
    ((ev₀ ◁ first-edge) ∙ Cone.match (conePre σ (source-cone C)))

  TargetVertex : Set m
  TargetVertex = ((G.target-frame ⁻¹ ∙ H.target-frame) ∙ (ev₁ ◁ long-edge)) =₂
    ((ev₁ ◁ second-edge) ∙ Cone.match (conePre σ (target-cone C)))

  short-edges : MiddleVertex → ConeIso (conePre σ (triangle-cone C)) (expression-pair f g)
  short-edges middle = record
    { leftIso = first-edge ; rightIso = second-edge ; compatible = middle }

  source-compatible : (middle : MiddleVertex) → SourceVertex →
    (H.source-frame ∙ (ev₀ ◁ long-edge)) =₂
      MorphismExpression.source-frame (presented-expression f g σ (short-edges middle))
  source-compatible middle = vertex-from-corner F.source-frame H.source-frame
    (ev₀ ◁ long-edge) ((ev₀ ◁ first-edge) ∙ Cone.match (conePre σ (source-cone C)))

  target-compatible : (middle : MiddleVertex) → TargetVertex →
    (H.target-frame ∙ (ev₁ ◁ long-edge)) =₂
      MorphismExpression.target-frame (presented-expression f g σ (short-edges middle))
  target-compatible middle = vertex-from-corner G.target-frame H.target-frame
    (ev₁ ◁ long-edge) ((ev₁ ◁ second-edge) ∙ Cone.match (conePre σ (target-cone C)))

  presentation : MiddleVertex → SourceVertex → TargetVertex → CompositePresentation f g h
  presentation middle source target = record
    { triangle = σ
    ; short-edges = short-edges middle
    ; long-edge = record
      { comparison = long-edge
      ; source-compatible = source-compatible middle source
      ; target-compatible = target-compatible middle target } }

  composite-comparison : MiddleVertex → SourceVertex → TargetVertex →
    ExpressionIso (compose-expression f g) h
  composite-comparison middle source target = recognize-composite (presentation middle source target)
```

