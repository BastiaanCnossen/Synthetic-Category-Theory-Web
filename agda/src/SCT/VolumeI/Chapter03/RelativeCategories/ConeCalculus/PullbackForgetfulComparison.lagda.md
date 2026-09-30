# Comparing the whole forgetful pullback cone

Reflect the evaluated cone comparison through ordinary uncurrying. Its
two legs are the prescribed inverse matchings of the projection squares.
Retaining these images lets the pasting proof use the actual relative
postcomposition functors and their specified matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackForgetfulComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; inverse-composite)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (uncurryCone)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeReflection 𝒯 M ℱ using (reflect-cone-prescribed)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P using (module MappedCone; mappedCone)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionCartesian 𝒯 M ℱ P using (module Postcomposition)
import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackConeEvaluation as ConeEvaluation

module Forgetful {K C D E S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} {h : MAP E S} (u : FunctorOver f h) (v : FunctorOver g h) where
  module R = RelativePullback u v using (first; second; first-map; second-map; left-map; right-map)
  module Evaluated = ConeEvaluation.Evaluation 𝒯 M ℱ P k u v
    using (ordinary; forget; comparison; comparison-left; comparison-right; β₁; β₂)
  module CF = Postcomposition k R.first using (square; evaluated-matching-normal)
  module CS = Postcomposition k R.second using (square; evaluated-matching-normal)
  module Mapped = MappedCone K (pullbackCone R.left-map R.right-map)
    using (value; evaluate; evaluate-left; evaluate-right)
  target = conePre Evaluated.forget Mapped.value
  left = Cone.match CF.square ⁻¹
  right = Cone.match CS.square ⁻¹
  evaluated : ConeIso (uncurryCone Evaluated.ordinary) (uncurryCone target)
  evaluated = coneIso-compose (coneIso-inverse (Mapped.evaluate Evaluated.forget)) Evaluated.comparison
  abstract
    left-normal : funUncurryIso left =₂
      ((funPost-uncurry R.first-map Evaluated.forget) ⁻¹ ∙ Evaluated.β₁)
    left-normal = isoComp-cong (idIso ((funPost-uncurry R.first-map Evaluated.forget) ⁻¹))
      (inverse-inverse Evaluated.β₁) ∙
      (inverse-composite (Evaluated.β₁ ⁻¹) (funPost-uncurry R.first-map Evaluated.forget) ∙
        ((＝-inv ◁ CF.evaluated-matching-normal) ∙ funUncurryIso-inverse (Cone.match CF.square)))
    right-normal : funUncurryIso right =₂
      ((funPost-uncurry R.second-map Evaluated.forget) ⁻¹ ∙ Evaluated.β₂)
    right-normal = isoComp-cong (idIso ((funPost-uncurry R.second-map Evaluated.forget) ⁻¹))
      (inverse-inverse Evaluated.β₂) ∙
      (inverse-composite (Evaluated.β₂ ⁻¹) (funPost-uncurry R.second-map Evaluated.forget) ∙
        ((＝-inv ◁ CS.evaluated-matching-normal) ∙ funUncurryIso-inverse (Cone.match CS.square)))
    left-image : ConeIso.leftIso evaluated =₂ funUncurryIso left
    left-image = left-normal ⁻¹ ∙
      isoComp-cong (＝-inv ◁ Mapped.evaluate-left Evaluated.forget) Evaluated.comparison-left
    right-image : ConeIso.rightIso evaluated =₂ funUncurryIso right
    right-image = right-normal ⁻¹ ∙
      isoComp-cong (＝-inv ◁ Mapped.evaluate-right Evaluated.forget) Evaluated.comparison-right
    comparison : ConeIso Evaluated.ordinary target
    comparison = reflect-cone-prescribed Evaluated.ordinary target evaluated left right left-image right-image
    comparison-left : ConeIso.leftIso comparison =₂ left
    comparison-left = idIso left
    comparison-right : ConeIso.rightIso comparison =₂ right
    comparison-right = idIso right
```
