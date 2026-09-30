# Relative functor categories and relative pullbacks

Forget the base triangles and use the pullback square of ordinary
functor categories. The cartesian forgetful squares identify the two
relative constructions by pullback pasting. All cone comparisons in
this argument retain their specified matchings.

The resulting equivalence exports its first-projection comparison.
The second-projection and evaluation computations are separate laws.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.FunctorPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanCartesian 𝒯 P using (module CospanCartesian)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P using (mappedCone; fun-preserves-pullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionCartesian 𝒯 M ℱ P using (module Postcomposition)

module Preservation {K C D E S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} {h : MAP E S} (u : FunctorOver f h) (v : FunctorOver g h) where
  module R = RelativePullback u v using (category; projection; first; left-map; right-map)
  module U = Postcompose k u using (functor)
  module V = Postcompose k v using (functor)
  module First = Postcompose k R.first using (functor)
  module CU = Postcomposition k u using (square; square-isPullback)
  module CV = Postcomposition k v using (square; square-isPullback)
  module CF = Postcomposition k R.first using (square; square-isPullback)
  A = FunOver k f
  B = FunOver k g
  H = FunOver k h
  Source = FunOver k R.projection
  Target = Pullback U.functor V.functor
  forgetA = Over.forget k f
  forgetB = Over.forget k g
  forgetH = Over.forget k h
  ordinary-left = funPost {C = K} R.left-map
  ordinary-right = funPost {C = K} R.right-map
  ordinary = mappedCone K (pullbackCone R.left-map R.right-map)
  abstract
    ordinary-isPullback : IsPullback ordinary
    ordinary-isPullback = fun-preserves-pullback K _ (pullbackCone-isPullback R.left-map R.right-map)
  module Paste = Pasting forgetA ordinary-left ordinary-right ordinary ordinary-isPullback
  outer = Paste.Paste.flatten (coneSwap CF.square)
  abstract
    outer-isPullback : IsPullback outer
    outer-isPullback = Paste.paste-isPullback (coneSwap CF.square)
      (pullback-swap CF.square CF.square-isPullback)

  cospan : CospanMap U.functor V.functor (ordinary-left ∘ forgetA) ordinary-right
  cospan = record { left = id A ; right = forgetB ; base = forgetH
    ; leftSquare = Cone.match CU.square ∙ comp-unitʳ (ordinary-left ∘ forgetA)
    ; rightSquare = Cone.match CV.square }
  module Change = CospanMap cospan using (pullbackMap; pullbackMap-β; mapCone)
  module Cartesian = CospanCartesian cospan (id-isEquiv A) CV.square-isPullback
    using (pullbackMap-isEquiv)
  intermediate = Pullback (ordinary-left ∘ forgetA) ordinary-right
  backward = IsEquiv.inverse Cartesian.pullbackMap-isEquiv
  functor : MAP Source Target
  functor = backward ∘ pullbackLift outer
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (pullbackLift outer) backward outer-isPullback
      (equiv-inverse Cartesian.pullbackMap-isEquiv)
    change-comparison : (Change.pullbackMap ∘ functor) =₁ pullbackLift outer
    change-comparison = comp-unitˡ (pullbackLift outer) ∙
      (((IsEquiv.retractionIso Cartesian.pullbackMap-isEquiv) ⁻¹ ▷ pullbackLift outer) ∙
        (comp-assoc (pullbackLift outer) backward Change.pullbackMap) ⁻¹)
    outer-comparison : ConeIso
      (conePre functor (Change.mapCone (pullbackCone U.functor V.functor))) outer
    outer-comparison = coneIso-compose (pullbackLift-β outer)
      (coneIso-compose (cone-action (pullbackCone (ordinary-left ∘ forgetA) ordinary-right) change-comparison)
        (coneIso-compose (conePre-assoc functor Change.pullbackMap
          (pullbackCone (ordinary-left ∘ forgetA) ordinary-right))
          (coneIso-inverse (coneIso-pre functor Change.pullbackMap-β))))
    change-first : (pullback₁ {f = ordinary-left ∘ forgetA} {ordinary-right} ∘ Change.pullbackMap) =₁
      pullback₁ {f = U.functor} {V.functor}
    change-first = comp-unitˡ pullback₁ ∙ ConeIso.leftIso Change.pullbackMap-β
    inverse-first : (pullback₁ {f = U.functor} {V.functor} ∘ backward) =₁
      pullback₁ {f = ordinary-left ∘ forgetA} {ordinary-right}
    inverse-first = comp-unitʳ pullback₁ ∙
      ((pullback₁ ◁ (IsEquiv.retractionIso Cartesian.pullbackMap-isEquiv) ⁻¹) ∙
        (comp-assoc backward Change.pullbackMap pullback₁ ∙ (change-first ⁻¹ ▷ backward)))
    first-comparison : (pullback₁ {f = U.functor} {V.functor} ∘ functor) =₁ First.functor
    first-comparison = pullbackLift-β₁ outer ∙
      ((inverse-first ▷ pullbackLift outer) ∙ (comp-assoc (pullbackLift outer) backward pullback₁) ⁻¹)
```
