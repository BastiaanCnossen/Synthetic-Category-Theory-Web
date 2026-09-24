# Evaluating the four corners of a curried square

Double evaluation agrees with restriction to the corresponding corner,
using the pairing-based vertex identification and the actual reflected
side comparisons. This is the generic corner equation needed to preserve
endpoint frames when viewing a square as a morphism of arrows.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.SquareCornerEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.DoubleEvaluationCorners as Double
import SCT.VolumeI.Chapter02.Section02.RectangularCornerNormalization as Normalize
import SCT.VolumeI.Chapter02.Section02.CornerRestrictionEvaluation as Restriction
open import SCT.VolumeI.Chapter02.Section02.SquareCurryingCoordinates 𝒯 M ℱ using (coinsert)
open import SCT.VolumeI.Chapter01.Section04.SquareEvaluation 𝒯 M using (evaluate-square-cong)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

module At {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C)) (u v : Obj-abs [1]) where
  module D = Double.At 𝒯 M ℱ P I E W u v
  module N = Normalize.At 𝒯 M ℱ Γ [1] [1] u v
  module R = Restriction.At 𝒯 M ℱ I v u (coinsert u) (insert v)
    N.Goal.K.ObjectCorner.corner W
  matching = R.R.matching

  abstract
    comparison : D.boundary =₂ (matching ∙ (evaluate v ◁ D.H.comparison))
    comparison = cancel-left-reflect D.right
      (isoComp-assoc-at D.right matching (evaluate v ◁ D.H.comparison) ∙
        isoComp-cong (R.comparison ⁻¹) (idIso (evaluate v ◁ D.H.comparison)) ∙
        (isoComp-assoc-at R.evaluated D.left (evaluate v ◁ D.H.comparison)) ⁻¹ ∙
        isoComp-cong
          (evaluate-square-cong D.h D.ib D.V.Coordinate.restriction D.ia D.H.Coordinate.restriction
            N.comparison)
          (idIso (D.left ∙ (evaluate v ◁ D.H.comparison))) ∙ D.comparison)
```
