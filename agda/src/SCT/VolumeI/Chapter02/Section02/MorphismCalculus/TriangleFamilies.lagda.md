# Families of triangle witnesses

Transposing a triangle witness in `Fun Γ C` gives a triangle family
on `Γ`. Its middle, source, and target corners are transported as
whole comparisons, each retaining its matching. At this stage their
endpoint diagrams lie in `Fun One C`; evaluating those diagrams is a
separate step from transposition. The three `edge-agrees` statements
verify that the repeated edge comparisons in these corners agree.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  where

open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.CompositeWitnesses 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.TransposedCornerComparisons as Corners

middle-square : Square one zero d₂ d₀
middle-square = record { commute = face-middle ⁻¹ }

source-square : Square zero zero d₁ d₂
source-square = record { commute = face-bottom }

target-square : Square one one d₀ d₁
target-square = record { commute = face-top }

module TransposedWitness {Γ C : CAT} {x y z : Obj-abs (Fun Γ C)}
  {f : Morphism x y} {g : Morphism y z} {h : Morphism x z}
  (w : CompositeWitness f g h) where
  module W = CompositeWitness w
  module B = Boundary f g h
  module Middle = Corners.Corner 𝒯 M ℱ P middle-square W.triangle B.middle W.middle-comparison
  module Source = Corners.Corner 𝒯 M ℱ P source-square W.triangle B.source-corner W.source-comparison
  module Target = Corners.Corner 𝒯 M ℱ P target-square W.triangle B.target-corner W.target-comparison

  triangle : MAP Γ (Triangles C)
  triangle = funCurry (transpose W.triangle)

  middle-vertex : ConeIso (conePre triangle (functorOut middle-square C)) Middle.Boundary.value
  middle-vertex = Middle.comparison

  source-vertex : ConeIso (conePre triangle (functorOut source-square C)) Source.Boundary.value
  source-vertex = Source.comparison

  target-vertex : ConeIso (conePre triangle (functorOut target-square C)) Target.Boundary.value
  target-vertex = Target.comparison

  first-edge-agrees : ConeIso.leftIso middle-vertex =₂ ConeIso.rightIso source-vertex
  first-edge-agrees = (Source.comparison-right) ⁻¹ ∙ Middle.comparison-left

  second-edge-agrees : ConeIso.rightIso middle-vertex =₂ ConeIso.leftIso target-vertex
  second-edge-agrees = (Target.comparison-left) ⁻¹ ∙ Middle.comparison-right

  long-edge-agrees : ConeIso.leftIso source-vertex =₂ ConeIso.rightIso target-vertex
  long-edge-agrees = (Target.comparison-right) ⁻¹ ∙ Source.comparison-left

-- The universal evaluation family turns an absolute shape witness into
-- a family parametrized by all diagrams of that shape.
evaluation-transpose : (B C : CAT) → MAP B (Fun (Fun B C) C)
evaluation-transpose B C = untranspose funEval

module UniversalWitness {B : CAT} {x y z : Obj-abs B}
  {f : Morphism x y} {g : Morphism y z} {h : Morphism x z}
  (w : CompositeWitness f g h) (C : CAT) where
  witness : CompositeWitness
    (post-morphism (evaluation-transpose B C) f)
    (post-morphism (evaluation-transpose B C) g)
    (post-morphism (evaluation-transpose B C) h)
  witness = post-witness (evaluation-transpose B C) w
  open TransposedWitness witness public

  triangle-restriction-raw : (funUncurry triangle) =₁
    (funUncurry (funPre {D = C} (CompositeWitness.triangle w)))
  triangle-restriction-raw = (funPre-β (CompositeWitness.triangle w)) ⁻¹ ∙
    ((transpose-β funEval ▷ productMap (id (Fun B C)) (CompositeWitness.triangle w)) ∙
      (transpose-pre (CompositeWitness.triangle w) (evaluation-transpose B C) ∙
        funCurry-β (transpose (CompositeWitness.triangle witness))))

  triangle-restriction : triangle =₁ (funPre (CompositeWitness.triangle w))
  triangle-restriction = funIsoReflect _ _ triangle-restriction-raw

  triangle-restriction-β : funUncurryIso triangle-restriction =₂ triangle-restriction-raw
  triangle-restriction-β = funIsoReflect-β _ _ triangle-restriction-raw
```
