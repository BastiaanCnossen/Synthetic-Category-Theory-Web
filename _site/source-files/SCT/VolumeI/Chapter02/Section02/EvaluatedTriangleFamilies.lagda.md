# The three evaluated corners of a triangle family

Transposition gives a family of arrows with specified endpoint frames.
Evaluating each restriction cone preserves its corner comparison and the
agreement between repeated edges. The statements here concern those
converted cones. `TriangleFamilyPresentations` identifies their matchings
with the chosen Segal triangle cones and obtains a composite presentation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Interval

module SCT.VolumeI.Chapter02.Section02.EvaluatedTriangleFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Interval.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section02.TriangleFamilies 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
import SCT.VolumeI.Chapter02.Section02.TransposedCornerComparisons as Corners
import SCT.VolumeI.Chapter02.Section02.EndpointRestrictionCones as Conversion

module Family {Γ C : CAT} where
  open Conversion.Endpoints 𝒯 M ℱ P C

  object : Obj-abs (Fun Γ C) → MAP Γ C
  object x = e ∘ funCurry (transpose x)

  module Arrow {x y : Obj-abs (Fun Γ C)} (f : Morphism x y) where
    module F = Morphism f
    module Source = Corners.Edge 𝒯 M ℱ P F.diagram zero x F.source-identification
    module Target = Corners.Edge 𝒯 M ℱ P F.diagram one y F.target-identification

    as-expression : MorphismExpression (object x) (object y)
    as-expression = record
      { arrow = Source.family
      ; source-frame = frame zero Source.family Source.comparison
      ; target-frame = frame one Target.family Target.comparison }

  module Witness {x y z : Obj-abs (Fun Γ C)}
    {f : Morphism x y} {g : Morphism y z} {h : Morphism x z}
    (w : CompositeWitness f g h) where
    module T = TransposedWitness w
    module F = Morphism f
    module G = Morphism g
    module H = Morphism h
    module First = Arrow f
    module Second = Arrow g
    module Long = Arrow h
    module Middle = Conversion.Framed 𝒯 M ℱ P F.diagram G.diagram one zero y
      F.target-identification G.source-identification
    module Source = Conversion.Framed 𝒯 M ℱ P H.diagram F.diagram zero zero x
      H.source-identification F.source-identification
    module Target = Conversion.Framed 𝒯 M ℱ P G.diagram H.diagram one one z
      G.target-identification H.target-identification

    middle-cone = convert (conePre T.triangle (functorOut middle-square C))
    source-cone = convert (conePre T.triangle (functorOut source-square C))
    target-cone = coneSwap (convert (conePre T.triangle (functorOut target-square C)))

    middle-corner : ConeIso middle-cone Middle.target
    middle-corner = Middle.comparison T.middle-vertex

    source-corner : ConeIso source-cone Source.target
    source-corner = Source.comparison T.source-vertex

    target-corner-reversed : ConeIso target-cone (coneSwap Target.target)
    target-corner-reversed = coneIso-swap (Target.comparison T.target-vertex)

    first-edge = ConeIso.leftIso middle-corner
    second-edge = ConeIso.rightIso middle-corner
    long-edge = ConeIso.leftIso source-corner

    first-edge-agrees : first-edge =₂ ConeIso.rightIso source-corner
    first-edge-agrees = T.first-edge-agrees

    second-edge-agrees : second-edge =₂ ConeIso.rightIso target-corner-reversed
    second-edge-agrees = T.second-edge-agrees

    long-edge-agrees : long-edge =₂ ConeIso.leftIso target-corner-reversed
    long-edge-agrees = T.long-edge-agrees

    abstract
      middle-vertex :
        ((MorphismExpression.source-frame Second.as-expression ⁻¹ ∙
          MorphismExpression.target-frame First.as-expression) ∙ (ev₁ ◁ first-edge)) =₂
        ((ev₀ ◁ second-edge) ∙ Cone.match middle-cone)
      middle-vertex = ConeIso.compatible middle-corner

      source-vertex :
        ((MorphismExpression.source-frame First.as-expression ⁻¹ ∙
          MorphismExpression.source-frame Long.as-expression) ∙ (ev₀ ◁ long-edge)) =₂
        ((ev₀ ◁ first-edge) ∙ Cone.match source-cone)
      source-vertex = isoComp-cong
        (postWhisker ev₀ ◁ (first-edge-agrees ⁻¹)) (idIso (Cone.match source-cone)) ∙
        ConeIso.compatible source-corner

      target-matching : (Cone.match (coneSwap Target.target)) =₂
        (MorphismExpression.target-frame Second.as-expression ⁻¹ ∙
          MorphismExpression.target-frame Long.as-expression)
      target-matching = isoComp-cong (idIso (Target.left-frame ⁻¹))
        (inverse-inverse Target.right-frame) ∙
        inverse-composite (Target.right-frame ⁻¹) Target.left-frame

      target-vertex :
        ((MorphismExpression.target-frame Second.as-expression ⁻¹ ∙
          MorphismExpression.target-frame Long.as-expression) ∙ (ev₁ ◁ long-edge)) =₂
        ((ev₁ ◁ second-edge) ∙ Cone.match target-cone)
      target-vertex = isoComp-cong
        (postWhisker ev₁ ◁ (second-edge-agrees ⁻¹)) (idIso (Cone.match target-cone)) ∙
        (ConeIso.compatible target-corner-reversed ∙
          isoComp-cong (target-matching ⁻¹) (postWhisker ev₁ ◁ long-edge-agrees))
```
