# Base change of factored evaluation squares

Factor endpoint evaluation through specified one-sided pullbacks. A
pullback of categories induces a pullback square between these evaluation
factorizations. The proof retains the full comparison defining the induced
map and the prescribed projection of its commutativity identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P using (mappedCone)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P using (fun-preserves-pullback)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Cospans
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalConeLifting as Lifting
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.CrossedEvaluationCones as Crossed

module At {T C D B X V W : CAT} (z : Obj-abs T) {f : MAP C B} {v : MAP D B}
  (s : Cone f v X) (es : IsPullback s)
  (a₀ : Cone (evaluate z) (Cone.right s) V) (ea : IsPullback a₀)
  (b₀ : Cone (evaluate z) f W) (eb : IsPullback b₀) where
  module Cross = Crossed.At 𝒯 M ℱ P z s
    using (cospan; square; crossed-comparison; module Coordinate)
  module Coordinate = Cross.Coordinate.Normal using (read; read-iso; read-pre)
  module Target = UniversalCone b₀ eb using (factor; factor-β)
  u = Cone.left s
  p = Cone.right s
  a₁ = Cone.left a₀
  b₁ = Cone.left b₀
  h : MAP V W
  h = Target.factor (Coordinate.read a₀)
  βh : ConeIso (conePre h b₀) (Coordinate.read a₀)
  βh = Target.factor-β (Coordinate.read a₀)
  ℓ = ConeIso.leftIso βh
  mapped-comparison = coneIso-compose (coneIso-inverse (Cross.Coordinate.comparison a₀)) βh
  module Lower = Cospans.Specified 𝒯 P Cross.cospan es a₀ ea b₀ eb h mapped-comparison
    using (projectionSquare; projection-square-isPullback)

  lower-square : Cone b₁ (funPost v) V
  lower-square = record { left = h ; right = a₁ ; match = ℓ }
  abstract
    lower-isPullback : IsPullback lower-square
    lower-isPullback = pullback-cone-invariant
      (cone-match-change _ _ _ _
        (isoComp-unitˡ-at ℓ ∙
          (isoComp-cong (inverse-identity _) (idIso ℓ) ∙
            inverse-inverse (ConeIso.leftIso mapped-comparison))))
      (pullback-swap Lower.projectionSquare Lower.projection-square-isPullback)

  module Factors (dₚ : MAP (Fun T X) V) (dₓ : MAP (Fun T C) W)
    (βp : ConeIso (conePre dₚ a₀) (Cross.square p))
    (βf : ConeIso (conePre dₓ b₀) (Cross.square f)) where
    Fu : MAP (Fun T X) (Fun T C)
    Fu = funPost u
    Fv : MAP (Fun T D) (Fun T B)
    Fv = funPost v
    arrow-cone = mappedCone T s
    Ω = Cone.match arrow-cone
    Kp = ConeIso.leftIso βp
    Kf = ConeIso.leftIso βf
    restricted-h = coneIso-compose (coneIso-pre dₚ βh)
      (coneIso-inverse (conePre-assoc dₚ h b₀))
    restricted-f = coneIso-compose (coneIso-pre Fu βf)
      (coneIso-inverse (conePre-assoc Fu dₓ b₀))
    first = coneIso-compose (coneIso-inverse (Coordinate.read-pre dₚ a₀)) restricted-h
    second = coneIso-compose (Coordinate.read-iso βp) first
    third = coneIso-compose Cross.crossed-comparison second
    whole = coneIso-compose (coneIso-inverse restricted-f) third
    module Lift = Lifting.UniversalLift 𝒯 P b₀ eb (h ∘ dₚ) (dₓ ∘ Fu) whole
      using (lift; left-image)
    χ = Lift.lift
    Jf = ConeIso.leftIso restricted-f
    L = (Fv ◁ Kp) ∙ Cone.match (conePre dₚ lower-square)
    module Cancel = Cancellation.Framed 𝒯 P dₓ b₁ Fv Kf
      lower-square lower-isPullback arrow-cone (fun-preserves-pullback T s es)
      using (edge-cone; module WithComparison)

    abstract
      first-left : ConeIso.leftIso first =₂ Cone.match (conePre dₚ lower-square)
      first-left = isoComp-cong (inverse-inverse (comp-assoc dₚ a₁ Fv))
        (idIso (ConeIso.leftIso restricted-h))
      lifted-left : (b₁ ◁ χ) =₂ (Jf ⁻¹ ∙ (Ω ⁻¹ ∙ L))
      lifted-left = isoComp-cong (idIso (Jf ⁻¹))
        (isoComp-cong (idIso (Ω ⁻¹)) (isoComp-cong (idIso (Fv ◁ Kp)) first-left)) ∙ Lift.left-image
      compatible :
        (Cone.match Cancel.edge-cone ∙ (b₁ ◁ χ)) =₂
        ((Fv ◁ Kp) ∙ Cone.match (conePre dₚ lower-square))
      compatible = cancel-inverse Ω L ∙
        (isoComp-cong (idIso Ω) (cancel-inverse Jf (Ω ⁻¹ ∙ L)) ∙
        (isoComp-assoc-at Ω Jf (Jf ⁻¹ ∙ (Ω ⁻¹ ∙ L)) ∙
          isoComp-cong (idIso (Ω ∙ Jf)) lifted-left))
    comparison : ConeIso (conePre dₚ lower-square) Cancel.edge-cone
    comparison = record { leftIso = χ ; rightIso = Kp ; compatible = compatible }
    module Result = Cancel.WithComparison dₚ comparison using (square; square-isPullback)
    open Result public using (square; square-isPullback)
```
