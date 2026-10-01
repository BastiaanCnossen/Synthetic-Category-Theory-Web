# Base change of left and right fibrations

For `prop:Left_Fibrations_Closed_Under_Base_Change`, apply the endpoint
pullback criterion to a specified pullback square. The functor category
preserves that square. Paste it with the evaluation square of the original
fibration, compare the two outside rectangles using the full evaluated
cone comparison, and cancel the original pullback square.

This proves closure for either variance. The comparison of directed
evaluation maps under base change and compatibility of transport are
separate statements.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.BaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-swap; coneSwap-pre; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯
  using (compositeCone; compositeCone-compatible)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse; inverse-identity)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P using (mappedCone)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P using (fun-preserves-pullback)
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.MappedEvaluationCones as Evaluated

module At (z : Obj-abs [1]) where
  square : {A B : CAT} (f : MAP A B) → Cone (evaluate {C = B} z) f (Ar A)
  square f = record { left = funPost f ; right = evaluate z ; match = evaluate-post z f }

  module Pullback {A B D X : CAT} {f : MAP A D} {v : MAP B D}
    (s : Cone f v X) (es : IsPullback s) (ef : IsPullback (square f)) where
    u = Cone.left s
    p = Cone.right s
    t = mappedCone [1] s
    Fp = funPost {C = [1]} p
    Fu = funPost {C = [1]} u
    e = evaluate {C = B} z
    module KnownPaste = Pasting.Pasting 𝒯 P (funPost v) (evaluate z) f (square f) ef
    module BasePaste = Pasting.Pasting 𝒯 P e v f (coneSwap s) (pullback-swap s es)
    known = changeLeft (evaluate-post z v) (KnownPaste.Paste.flatten (coneSwap t))
    wanted = BasePaste.Paste.flatten (square p)
    module EC = Evaluated.At 𝒯 M ℱ P z t
    module MC = Evaluated.MappedAt 𝒯 M ℱ P z s
    c₀ = evaluate-post-at z f Fu
    W = evaluate z ◁ Cone.match t
    A₀ = comp-assoc Fp (funPost v) (evaluate z)
    B₀ = comp-assoc Fp e v
    j = evaluate-post z v ▷ Fp
    common = c₀ ∙ (W ⁻¹ ∙ (A₀ ∙ (j ⁻¹ ∙ B₀ ⁻¹)))

    abstract
      known-normal : Cone.match (compositeCone e v known) =₂ common
      known-normal = isoComp-cong (idIso c₀)
          (isoComp-assoc-at (W ⁻¹) A₀ (j ⁻¹ ∙ B₀ ⁻¹)) ∙
        isoComp-assoc-at c₀ (W ⁻¹ ∙ A₀) (j ⁻¹ ∙ B₀ ⁻¹) ∙
        isoComp-assoc-at (c₀ ∙ (W ⁻¹ ∙ A₀)) (j ⁻¹) (B₀ ⁻¹) ∙
        isoComp-cong
          (isoComp-cong
            (isoComp-cong (idIso c₀)
              (isoComp-cong (post-inverse (evaluate z) (Cone.match t)) (idIso A₀)))
            (idIso (j ⁻¹)))
          (idIso (B₀ ⁻¹))

      right-inverse : ((B₀ ∙ (j ∙ A₀ ⁻¹)) ⁻¹) =₂ (A₀ ∙ (j ⁻¹ ∙ B₀ ⁻¹))
      right-inverse = isoComp-assoc-at A₀ (j ⁻¹) (B₀ ⁻¹) ∙
        isoComp-cong
          (isoComp-cong (inverse-inverse A₀) (idIso (j ⁻¹)) ∙ inverse-composite j (A₀ ⁻¹))
          (idIso (B₀ ⁻¹)) ∙
        inverse-composite B₀ (j ∙ A₀ ⁻¹)

      evaluated-normal : Cone.match (coneSwap EC.value) =₂ common
      evaluated-normal = isoComp-assoc-at c₀ (W ⁻¹) (A₀ ∙ (j ⁻¹ ∙ B₀ ⁻¹)) ∙
        isoComp-cong
          (isoComp-cong (inverse-inverse c₀) (idIso (W ⁻¹)) ∙ inverse-composite W (c₀ ⁻¹))
          right-inverse ∙
        inverse-composite (B₀ ∙ (j ∙ A₀ ⁻¹)) (W ∙ c₀ ⁻¹)

    normalization : ConeIso (compositeCone e v known) (coneSwap EC.value)
    normalization = cone-match-change _ _ _ _ (evaluated-normal ⁻¹ ∙ known-normal)

    raw-comparison : ConeIso (compositeCone e v known) (compositeCone e v wanted)
    raw-comparison = coneIso-compose (coneIso-inverse (BasePaste.Paste.flatten-composite (square p)))
      (coneIso-compose (coneIso-inverse (coneSwap-pre (evaluate z) s))
        (coneIso-compose (coneIso-swap MC.comparison) normalization))

    abstract
      left-normal : ConeIso.leftIso raw-comparison =₂ (e ◁ idIso Fp)
      left-normal = (postWhisker-idIso e Fp) ⁻¹ ∙ isoComp-inverseˡ-at b ∙
        isoComp-cong (idIso (b ⁻¹))
          (isoComp-unitˡ-at b ∙
            isoComp-cong (inverse-identity (p ∘ evaluate z)) (isoComp-unitʳ-at b))
        where
        b : (e ∘ Fp) =₁ (p ∘ evaluate z)
        b = evaluate-post z p

      right-normal : ConeIso.rightIso raw-comparison =₂ evaluate-post z u
      right-normal = isoComp-unitˡ-at a₀ ∙
        isoComp-cong (inverse-identity (u ∘ evaluate z))
          (isoComp-unitˡ-at a₀ ∙
            isoComp-cong (inverse-identity (u ∘ evaluate z)) (isoComp-unitʳ-at a₀))
        where
        a₀ : (evaluate z ∘ Fu) =₁ (u ∘ evaluate z)
        a₀ = evaluate-post z u

    adjusted = coneIso-adjust raw-comparison (e ◁ idIso Fp) (evaluate-post z u)
      left-normal right-normal

    comparison : ConeIso known wanted
    comparison = compositeCone-compatible e v known wanted (idIso Fp) (evaluate-post z u)
      (ConeIso.compatible adjusted)

    abstract
      square-isPullback : IsPullback (square p)
      square-isPullback = BasePaste.cancel-isPullback (square p)
        (pullback-cone-invariant comparison
          (ArrowChange.ChangeLeft.preserve 𝒯 P (evaluate-post z v) f
            (KnownPaste.Paste.flatten (coneSwap t))
            (KnownPaste.paste-isPullback (coneSwap t)
              (pullback-swap t (fun-preserves-pullback [1] s es)))))

left-base-change : {A B D X : CAT} {f : MAP A D} {v : MAP B D}
  (s : Cone f v X) → IsPullback s → IsEquiv (Evaluation.directed-ev₀ f) →
  IsEquiv (Evaluation.directed-ev₀ (Cone.right s))
left-base-change {f = f} s es ef = Criterion.pullback-to-left (Cone.right s)
  (At.Pullback.square-isPullback zero s es (Criterion.left-to-pullback f ef))

right-base-change : {A B D X : CAT} {f : MAP A D} {v : MAP B D}
  (s : Cone f v X) → IsPullback s → IsEquiv (Evaluation.directed-ev₁ f) →
  IsEquiv (Evaluation.directed-ev₁ (Cone.right s))
right-base-change {f = f} s es ef = Criterion.pullback-to-right (Cone.right s)
  (At.Pullback.square-isPullback one s es (Criterion.right-to-pullback f ef))
```
