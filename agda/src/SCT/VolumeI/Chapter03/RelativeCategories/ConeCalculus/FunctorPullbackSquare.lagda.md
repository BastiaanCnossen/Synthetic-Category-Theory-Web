# Relative functor categories preserve the specified pullback

Paste the relative square with the cartesian forgetful square for its
right arrow. The evaluated whole-cone comparison identifies the result
with the ordinary functor-category pullback pasted with the first
projection square. Pullback pasting and cancellation prove the claim for
the actual matching constructed from the relative pullback.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.FunctorPullbackSquare
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; inverse-identity; pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; coneSwap-pre; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionCartesian 𝒯 M ℱ P using (module Postcomposition)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackMatching 𝒯 M ℱ P using (module Matching)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.FunctorPullbacks 𝒯 M ℱ P using (module Preservation)
import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackConeEvaluation as ConeEvaluation
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackForgetfulComparison 𝒯 M ℱ P using (module Forgetful)

module Square {K C D E S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} {h : MAP E S} (u : FunctorOver f h) (v : FunctorOver g h) where
  module R = RelativePullback u v using (projection; first; second; right-map; left-map)
  module U = Postcompose k u using (functor)
  module First = Postcompose k R.first using (functor)
  module Second = Postcompose k R.second using (functor)
  module CU = Postcomposition k u using (square)
  module CV = Postcomposition k v using (square; square-isPullback)
  module CF = Postcomposition k R.first using (square)
  module CS = Postcomposition k R.second using (square)
  module Match = Matching k u v using (cone; matching)
  module Existing = Preservation k u v using (outer; outer-isPullback; module Paste)
  module Evaluated = ConeEvaluation.Evaluation 𝒯 M ℱ P k u v using (ordinary)
  module Whole = Forgetful k u v using (comparison; comparison-left; comparison-right)
  forgetA = Over.forget k f
  forgetH = Over.forget k h
  ordinary-left = funPost {C = K} R.left-map
  ordinary-right = funPost {C = K} R.right-map
  module RightPaste = Pasting U.functor forgetH ordinary-right (coneSwap CV.square)
    (pullback-swap CV.square CV.square-isPullback)
    using (module Paste; cancel-isPullback)
  rectangle = RightPaste.Paste.flatten Match.cone
  change = Cone.match CU.square ⁻¹
  changed = changeLeft change rectangle
  outer = Existing.outer
  reduced = compositeCone forgetA ordinary-left changed
  reduced-outer = compositeCone forgetA ordinary-left outer
  qu = Cone.match (conePre First.functor CU.square)
  qv = Cone.match (conePre Second.functor CV.square)
  ν = Cone.match (conePre Second.functor (coneSwap CV.square))
  δ = forgetH ◁ Match.matching
  A = comp-assoc First.functor U.functor forgetH
  B′ = Cone.match CU.square ▷ First.functor
  C′ = comp-assoc First.functor forgetA ordinary-left
  swapped = coneSwap-pre Second.functor CV.square

  abstract
    swap-normal : ν =₂ (qv ⁻¹)
    swap-normal = isoComp-unitʳ-at (qv ⁻¹) ∙
      (isoComp-cong (idIso (qv ⁻¹)) (postWhisker-idIso forgetH _) ∙
        ((ConeIso.compatible swapped) ⁻¹ ∙
          (isoComp-cong ((postWhisker-idIso ordinary-right _) ⁻¹) (idIso ν) ∙
            (isoComp-unitˡ-at ν) ⁻¹)))
    change-normal : ((change ▷ First.functor) ⁻¹) =₂ B′
    change-normal = inverse-inverse B′ ∙ (＝-inv ◁ pre-inverse (Cone.match CU.square) First.functor)
    reduced-match : Cone.match reduced =₂ Cone.match Evaluated.ordinary
    reduced-match =
      isoComp-cong (idIso (qv ⁻¹)) (isoComp-assoc-at δ A (B′ ∙ C′ ⁻¹)) ∙
      (isoComp-cong (idIso (qv ⁻¹)) (isoComp-assoc-at (δ ∙ A) B′ (C′ ⁻¹)) ∙
        (isoComp-assoc-at (qv ⁻¹) ((δ ∙ A) ∙ B′) (C′ ⁻¹) ∙
          (isoComp-cong (isoComp-assoc-at (qv ⁻¹) (δ ∙ A) B′) (idIso (C′ ⁻¹)) ∙
            isoComp-cong
              (isoComp-cong (isoComp-cong swap-normal (idIso (δ ∙ A))) change-normal)
              (idIso (C′ ⁻¹)))))
    reduced-comparison : ConeIso reduced Evaluated.ordinary
    reduced-comparison = cone-match-change _ _ _ _ reduced-match

  outer-image = Existing.Paste.Paste.flatten-composite (coneSwap CF.square)
  raw = coneIso-compose (coneIso-inverse outer-image)
    (coneIso-compose Whole.comparison reduced-comparison)
  right = Cone.match CS.square ⁻¹
  left = forgetA ◁ idIso First.functor
  abstract
    left-normal : ConeIso.leftIso raw =₂ left
    left-normal = (postWhisker-idIso forgetA First.functor) ⁻¹ ∙
      (isoComp-inverseˡ-at (Cone.match CF.square ⁻¹) ∙
        isoComp-cong (idIso ((Cone.match CF.square ⁻¹) ⁻¹))
          (isoComp-unitʳ-at (Cone.match CF.square ⁻¹) ∙
            isoComp-cong Whole.comparison-left (idIso (idIso (forgetA ∘ First.functor)))))
    right-normal : ConeIso.rightIso raw =₂ right
    right-normal = isoComp-unitˡ-at right ∙
      isoComp-cong (inverse-identity _)
        (isoComp-unitʳ-at right ∙ isoComp-cong Whole.comparison-right (idIso (idIso _)))
    rectangle-comparison : ConeIso changed outer
    rectangle-comparison = compositeCone-compatible forgetA ordinary-left changed outer
      (idIso First.functor) right
      (ConeIso.compatible (coneIso-adjust raw left right left-normal right-normal))
    isPullback : IsPullback Match.cone
    isPullback = RightPaste.cancel-isPullback Match.cone
      (ChangeLeft.reflect change ordinary-right rectangle
        (pullback-cone-invariant (coneIso-inverse rectangle-comparison) Existing.outer-isPullback))
```
