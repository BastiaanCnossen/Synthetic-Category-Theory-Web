# The evaluation corner and the Segal cone

For a family of squares, the target evaluation square of source evaluation
is the upper triangle's Segal cone. The comparison uses the specified
double-evaluation corner, so it retains the commutativity identification
as well as the two edge comparisons.

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

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEvaluationCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S
  using (triangle-cone)
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareShape 𝒯 M ℱ P I E
  using (j₀; j₁)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
  using (coneIso-compose)
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurrying as Currying
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCornerEvaluation as Corner
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareBoundaryCones as Boundaries
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointFrameCones as Frames
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.InsertedShapeCorners as Shape
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates 𝒯 M ℱ
  using (coinsert)
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.FramedCornerPasting 𝒯 M ℱ P
  using (inverse-quotient)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-swap; coneSwap-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
  using (coneIso-inverse)

module At {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C)) where
  module Curried = Currying.At 𝒯 M ℱ W using (nested; module Horizontal; module Vertical)
  module H = Curried.Horizontal zero using (comparison)
  module V = Curried.Vertical one using (boundary)
  module B = Boundaries.At.UpperMiddle 𝒯 M ℱ P I E W
    using (comparison; module Framing; module Corner)
  module K = Corner.At 𝒯 M ℱ P I E W zero one using (comparison)

  corner : ConeIso
    (conePre Curried.nested (Criterion.target-square (ev₀ {C})))
    B.Framing.Restricted.target
  corner = record
    { leftIso = H.comparison
    ; rightIso = V.boundary
    ; compatible = K.comparison ⁻¹ ∙
        isoComp-cong (B.Framing.matching ⁻¹) (idIso (ev₁ ◁ H.comparison)) }

  comparison : ConeIso
    (conePre Curried.nested (Criterion.target-square (ev₀ {C})))
    (conePre (funPre j₀ ∘ W) (triangle-cone C))
  comparison = coneIso-compose B.comparison corner

module Dual {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C)) where
  module Curried = Currying.At 𝒯 M ℱ W using (nested; module Horizontal; module Vertical)
  module H = Curried.Horizontal one using (comparison)
  module V = Curried.Vertical zero using (boundary)
  module B = Boundaries.At.LowerMiddle 𝒯 M ℱ P I E W
    using (comparison; module Framing)
  module K = Corner.At 𝒯 M ℱ P I E W one zero using (comparison; matching)
  module Vertex = Shape.Vertex 𝒯 M ℱ one zero using (horizontal-frame; vertical-frame)
  module Framing = Frames.At 𝒯 M ℱ P (coinsert one) (insert zero) zero one
    Vertex.horizontal-frame Vertex.vertical-frame W using (matching)

  corner : ConeIso
    (conePre Curried.nested (Criterion.source-square (ev₁ {C})))
    (coneSwap B.Framing.Restricted.target)
  corner = record
    { leftIso = H.comparison
    ; rightIso = V.boundary
    ; compatible = K.comparison ⁻¹ ∙
        isoComp-cong (Framing.matching ⁻¹ ∙
          inverse-quotient B.Framing.Restricted.left-frame B.Framing.Restricted.right-frame)
          (idIso (ev₀ ◁ H.comparison)) }

  comparison : ConeIso
    (conePre Curried.nested (Criterion.source-square (ev₁ {C})))
    (conePre (funPre j₁ ∘ W) (coneSwap (triangle-cone C)))
  comparison = coneIso-compose (coneIso-inverse (coneSwap-pre (funPre j₁ ∘ W) (triangle-cone C)))
    (coneIso-compose (coneIso-swap B.comparison) corner)
```
