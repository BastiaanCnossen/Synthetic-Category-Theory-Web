# Evaluating the base-change cone at a point

The cone defining base change of a universal family restricts to the
ordinary cone defining base change of its value at a point. The matching
calculation uses the point-restriction square and naturality in the
original cone's specified matching identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter03.Section05.Currying.PointRestrictionOverBase as PointRestriction

module SCT.VolumeI.Chapter03.Section05.Currying.PointPullbackCone
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (restriction-over)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies 𝒯 M ℱ P using (point-parameter)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
module PS = Projections 𝒯

module At {X C S T A : CAT} (z : Obj-abs X) {f : MAP C T} {p : MAP S T} (s : Cone f p A) where
  r : MAP A C
  r = Cone.left s
  q : MAP A S
  q = Cone.right s
  τ : (f ∘ r) =₁ (p ∘ q)
  τ = Cone.match s
  module Restriction = PointRestriction.Over 𝒯 M ℱ P z r f
  module Source = Restriction.Square.Source
  module Target = Restriction.Square.Target
  K : MAP A (X × A)
  K = Source.K
  R : MAP (X × A) (X × C)
  R = Restriction.Square.R
  br : ((f ∘ r) ∘ pr₂ {C = X}) =₁ (f ∘ (r ∘ pr₂))
  br = comp-assoc pr₂ r f
  bq : ((p ∘ q) ∘ pr₂ {C = X}) =₁ (p ∘ (q ∘ pr₂))
  bq = comp-assoc pr₂ q p
  bR : ((f ∘ pr₂) ∘ R) =₁ (f ∘ (r ∘ pr₂))
  bR = restriction-over X r f

  parameterized : Cone (f ∘ pr₂ {C = X}) p (X × A)
  parameterized = record { left = R ; right = q ∘ pr₂
    ; match = bq ∙ ((τ ▷ pr₂) ∙ ((br ⁻¹) ∙ bR)) }
  target : Cone (f ∘ pr₂ {C = X}) p A
  target = Action.value p (point-parameter f z) s
  κ : ((f ∘ pr₂) ∘ (R ∘ K)) =₁ (((f ∘ pr₂) ∘ R) ∘ K)
  κ = (comp-assoc K R (f ∘ pr₂)) ⁻¹
  rq : (((p ∘ q) ∘ pr₂ {C = X}) ∘ K) =₁ (p ∘ q)
  rq = PS.lift-base p (q ∘ pr₂) K (Source.triangle q) ∙ (bq ▷ K)
  τi : (((f ∘ r) ∘ pr₂ {C = X}) ∘ K) =₁ (((p ∘ q) ∘ pr₂ {C = X}) ∘ K)
  τi = (τ ▷ pr₂) ▷ K
  lower : ((f ∘ (r ∘ pr₂ {C = X})) ∘ K) =₁ (f ∘ r)
  lower = PS.lift-base f (r ∘ pr₂) K (Source.triangle r)

  abstract
    match-at-point : (Cone.match parameterized ▷ K) =₂
      ((bq ▷ K) ∙ (τi ∙ ((br ▷ K) ⁻¹ ∙ (bR ▷ K))))
    match-at-point = isoComp-cong (idIso (bq ▷ K))
        (isoComp-cong (idIso τi)
          (isoComp-cong (pre-inverse br K) (idIso (bR ▷ K)) ∙ preWhisker-isoComp-at (br ⁻¹) bR K) ∙
          preWhisker-isoComp-at (τ ▷ pr₂) (br ⁻¹ ∙ bR) K) ∙
      preWhisker-isoComp-at bq ((τ ▷ pr₂) ∙ (br ⁻¹ ∙ bR)) K

    regroup :
      ((p ◁ Source.triangle q) ∙ Cone.match (conePre K parameterized)) =₂
      (rq ∙ (τi ∙ ((br ▷ K) ⁻¹ ∙ ((bR ▷ K) ∙ κ))))
    regroup =
      (isoComp-assoc-at
        (PS.lift-base p (q ∘ pr₂) K (Source.triangle q)) (bq ▷ K)
        (τi ∙ ((br ▷ K) ⁻¹ ∙ ((bR ▷ K) ∙ κ)))) ⁻¹ ∙
      (isoComp-cong (idIso (PS.lift-base p (q ∘ pr₂) K (Source.triangle q)))
        (isoComp-cong (idIso (bq ▷ K))
          (isoComp-cong (idIso τi) (isoComp-assoc-at ((br ▷ K) ⁻¹) (bR ▷ K) κ) ∙
            isoComp-assoc-at τi ((br ▷ K) ⁻¹ ∙ (bR ▷ K)) κ) ∙
          isoComp-assoc-at (bq ▷ K) (τi ∙ ((br ▷ K) ⁻¹ ∙ (bR ▷ K))) κ) ∙
        (isoComp-cong (idIso (PS.lift-base p (q ∘ pr₂) K (Source.triangle q)))
          (isoComp-cong match-at-point (idIso κ)) ∙
          (isoComp-assoc-at (p ◁ Source.triangle q) (comp-assoc K (q ∘ pr₂) p)
            ((Cone.match parameterized ▷ K) ∙ κ)) ⁻¹))

    right-normalization :
      ((p ◁ Source.triangle q) ∙ Cone.match (conePre K parameterized)) =₂
      (τ ∙ Restriction.source)
    right-normalization = isoComp-cong (idIso τ) ((Restriction.source-normalization) ⁻¹) ∙
      (isoComp-cong (idIso τ)
        (isoComp-cong
          (cancel-right (br ▷ K) lower ∙
            isoComp-cong (Source.composite r f) (idIso ((br ▷ K) ⁻¹)))
          (idIso ((bR ▷ K) ∙ κ)) ∙
          (isoComp-assoc-at (Source.triangle (f ∘ r)) ((br ▷ K) ⁻¹) ((bR ▷ K) ∙ κ)) ⁻¹) ∙
        (isoComp-assoc-at τ (Source.triangle (f ∘ r)) ((br ▷ K) ⁻¹ ∙ ((bR ▷ K) ∙ κ)) ∙
          (isoComp-cong (Source.outer τ) (idIso ((br ▷ K) ⁻¹ ∙ ((bR ▷ K) ∙ κ))) ∙
            ((isoComp-assoc-at (Source.triangle (p ∘ q)) τi ((br ▷ K) ⁻¹ ∙ ((bR ▷ K) ∙ κ))) ⁻¹ ∙
              (isoComp-cong ((Source.composite q p) ⁻¹)
                (idIso (τi ∙ ((br ▷ K) ⁻¹ ∙ ((bR ▷ K) ∙ κ)))) ∙ regroup)))))

  comparison : ConeIso (conePre K parameterized) target
  comparison = record
    { leftIso = Restriction.Square.comparison ; rightIso = Source.triangle q
    ; compatible = right-normalization ⁻¹ ∙
        (isoComp-cong (idIso τ) Restriction.projection ∙
          isoComp-assoc-at τ Restriction.target ((f ∘ pr₂) ◁ Restriction.Square.comparison)) }
```
