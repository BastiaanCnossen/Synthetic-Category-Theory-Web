# Transverse evaluation-cone comparisons

Evaluating a mapped cone compares its naturality square with the original
cone. Rotating this comparison gives the transverse comparison used in
base change of directed evaluation. Its two legs are the specified inverse
matching of the mapped cone and the inverse evaluation comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.CrossedEvaluationCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P using (mappedCone)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.SquareRotation 𝒯 using (rotate)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Coordinates
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Action
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.MappedEvaluationCones as Evaluated

module At {T C D B X : CAT} (z : Obj-abs T) {f : MAP C B} {v : MAP D B}
  (s : Cone f v X) where
  u = Cone.left s
  p = Cone.right s
  Ω = Cone.match (mappedCone T s)
  square : {A B′ : CAT} (k : MAP A B′) → Cone (evaluate z) k (Fun T A)
  square k = record { left = funPost k ; right = evaluate z ; match = evaluate-post z k }
  cospan : CospanMap (evaluate {C = D} z) p (evaluate {C = B} z) f
  cospan = record
    { left = funPost v ; right = u ; base = v
    ; leftSquare = evaluate-post z v ; rightSquare = Cone.match s }
  module Normalize = Action.Action 𝒯 P cospan using (normalized; module Normalization)
  module Coordinate = Coordinates.Action 𝒯 P cospan using (module Normal; comparison)
  module Original = Evaluated.MappedAt 𝒯 M ℱ P z s using (comparison)
  A₀ = evaluate-post-at z f (funPost u)
  B₀ = evaluate-post-at z v (funPost p)
  X₀ = f ◁ evaluate-post z u
  Y₀ = v ◁ evaluate-post z p
  Q₀ = evaluate z ◁ Ω
  W₀ = Cone.match (conePre (evaluate z) s)

  abstract
    normalized-comparison : ConeIso (Normalize.normalized (square p)) (conePre (funPost u) (square f))
    normalized-comparison = record
      { leftIso = Ω ⁻¹ ; rightIso = (evaluate-post z u) ⁻¹
      ; compatible =
          isoComp-cong ((post-inverse f (evaluate-post z u)) ⁻¹)
            (idIso (Cone.match (Normalize.normalized (square p)))) ∙
          (rotate A₀ Q₀ B₀ Y₀ W₀ X₀ (ConeIso.compatible Original.comparison) ∙
            isoComp-cong (idIso A₀) (post-inverse (evaluate z) Ω)) }

    comparison : ConeIso (CospanMap.mapCone cospan (square p)) (conePre (funPost u) (square f))
    comparison = coneIso-compose normalized-comparison
      (coneIso-inverse (cone-match-change _ _ _ _ (Normalize.Normalization.matching (square p))))

    comparison-left : ConeIso.leftIso comparison =₂ (Ω ⁻¹)
    comparison-left = isoComp-unitʳ-at (Ω ⁻¹) ∙ isoComp-cong (idIso (Ω ⁻¹)) (inverse-identity _)
    comparison-right : ConeIso.rightIso comparison =₂ ((evaluate-post z u) ⁻¹)
    comparison-right = isoComp-unitʳ-at ((evaluate-post z u) ⁻¹) ∙
      isoComp-cong (idIso ((evaluate-post z u) ⁻¹)) (inverse-identity _)

    coordinate-raw : ConeIso (Coordinate.Normal.read (square p)) (conePre (funPost u) (square f))
    coordinate-raw = coneIso-compose comparison
      (coneIso-inverse (Coordinate.comparison (square p)))
    coordinate-compatible :
      (Cone.match (conePre (funPost u) (square f)) ∙ (evaluate z ◁ (Ω ⁻¹))) =₂
      ((f ◁ ((evaluate-post z u) ⁻¹)) ∙ Cone.match (Coordinate.Normal.read (square p)))
    coordinate-compatible = ConeIso.compatible
      (coneIso-adjust coordinate-raw (Ω ⁻¹) ((evaluate-post z u) ⁻¹)
        (isoComp-unitʳ-at (Ω ⁻¹) ∙ isoComp-cong comparison-left (inverse-identity _))
        (isoComp-unitʳ-at ((evaluate-post z u) ⁻¹) ∙ isoComp-cong comparison-right (inverse-identity _)))

  crossed-comparison : ConeIso (Coordinate.Normal.read (square p)) (conePre (funPost u) (square f))
  crossed-comparison = record
    { leftIso = Ω ⁻¹ ; rightIso = (evaluate-post z u) ⁻¹
    ; compatible = coordinate-compatible }
```
