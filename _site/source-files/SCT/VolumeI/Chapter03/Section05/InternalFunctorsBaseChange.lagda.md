# Internal functor categories commute with base change

For `obs:Relative_Functor_Categories_Compatible_With_Pullback`, first
base change the dependent product defining the internal functor category.
The two pullback targets are equivalent over the new source category.
Transport evaluation across this equivalence and apply uniqueness of
dependent products. The resulting comparison retains its base triangle,
which supplies the displayed pullback square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorsBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.InternalFunctors 𝒯 M ℱ P using (module FunctorCategory)
open import SCT.VolumeI.Chapter03.Section05.DependentProductsBaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.PullbackTargetsBaseChange 𝒯 M ℱ P using (module Targets)
open import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences 𝒯 M ℱ P using (module Inverse)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.DependentProductTargetTransport 𝒯 M ℱ P using (module Transport)
open import SCT.VolumeI.Chapter03.Section05.DependentProductUniqueness 𝒯 M ℱ P using (module Uniqueness)

module ChangeBase {C D S T : CAT} (p : MAP C S) (q : MAP D S)
  (ep : IsExponentiable p) (t : MAP T S) where
  module TargetData = Targets p q t
    using (p′; q′; f; h; old-projection; new-projection; forward; forward-isEquiv)
  open TargetData using (p′; q′; f; h)
  square = pullbackCone p t
  abstract
    square-isPullback : IsPullback square
    square-isPullback = pullbackCone-isPullback p t
    ep′ : IsExponentiable p′
    ep′ = Exponentiable.AfterBaseChange.isExponentiable ep t square square-isPullback
  module Old = FunctorCategory p q ep using (category; projection; product)
  module New = FunctorCategory p′ q′ ep′ using (category; projection; product)
  module Pulled = BaseChange p t square square-isPullback f Old.product using (dependent-product)
  module Back = Inverse TargetData.forward TargetData.forward-isEquiv using (inverse; left-inverse; right-inverse)
  abstract
    backward-isEquiv : IsEquiv (FunctorLift.lift Back.inverse)
    backward-isEquiv = record
      { inverse = FunctorLift.lift TargetData.forward
      ; sectionIso = (FunctorOverIso.underlying Back.right-inverse) ⁻¹
      ; retractionIso = (FunctorOverIso.underlying Back.left-inverse) ⁻¹ }
  module Transported = Transport p′ TargetData.old-projection TargetData.new-projection
    Back.inverse backward-isEquiv Pulled.dependent-product using (dependent-product)
  module Unique = Uniqueness p′ TargetData.new-projection New.product Transported.dependent-product
    using (forward; forward-isEquiv)

  comparison : FunctorOver New.projection (pullback₂ {f = Old.projection} {t})
  comparison = Unique.forward
  functor : MAP New.category (Pullback Old.projection t)
  functor = FunctorLift.lift comparison
  triangle = FunctorLift.comparison comparison
  restricted = conePre functor (pullbackCone Old.projection t)
  cone : Cone Old.projection t New.category
  cone = record { left = Cone.left restricted ; right = New.projection
    ; match = (t ◁ triangle) ∙ Cone.match restricted }

  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = Unique.forward-isEquiv

    cone-comparison : ConeIso restricted cone
    cone-comparison = record { leftIso = idIso (Cone.left restricted) ; rightIso = triangle
      ; compatible = isoComp-unitʳ-at (Cone.match cone) ∙
          isoComp-cong (idIso (Cone.match cone)) (postWhisker-idIso Old.projection (Cone.left restricted)) }

    isPullback : IsPullback cone
    isPullback = pullback-cone-invariant cone-comparison
      (pullback-restrict-equivalence (pullbackCone Old.projection t) functor
        (pullbackCone-isPullback Old.projection t) functor-isEquiv)
```
