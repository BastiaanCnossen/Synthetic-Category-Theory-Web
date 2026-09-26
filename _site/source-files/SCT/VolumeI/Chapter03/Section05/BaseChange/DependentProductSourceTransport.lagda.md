# Transporting a dependent product along an equivalent source

A pullback square with an equivalence on its upper side transports
dependent products of arbitrary targets. Postcompose the target with
the equivalence, apply base change, and identify its pulled-back target
with the original target. All evaluations and base triangles are retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.DependentProductSourceTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (pullback-equivalence)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences 𝒯 M ℱ P using (module Inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductsBaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.DependentProductTargetTransport 𝒯 M ℱ P using (module Transport)

module Source {S T S′ T′ C : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (square-isPullback : IsPullback square)
  (source-isEquiv : IsEquiv (Cone.left square)) (f : MAP C S′)
  (Π : DependentProduct p (Cone.left square ∘ f)) where
  e = Cone.left square
  p′ = Cone.right square
  old-target = e ∘ f
  new-target : MAP (Pullback old-target e) S′
  new-target = pullback₂
  module Pulled = BaseChange p b square square-isPullback old-target Π
  cone : Cone old-target e C
  cone = record { left = id C ; right = f ; match = comp-unitʳ old-target }
  comparison : FunctorOver f new-target
  comparison = lift-triangle cone

  abstract
    comparison-isEquiv : IsEquiv (FunctorLift.lift comparison)
    comparison-isEquiv = equiv-cancel-left (FunctorLift.lift comparison) pullback₁
      (pullback-equivalence old-target e source-isEquiv)
      (equiv-transport ((pullbackLift-β₁ cone) ⁻¹) (id-isEquiv C))

  module Back = Inverse comparison comparison-isEquiv
  abstract
    backward-isEquiv : IsEquiv (FunctorLift.lift Back.inverse)
    backward-isEquiv = record { inverse = FunctorLift.lift comparison
      ; sectionIso = (FunctorOverIso.underlying Back.right-inverse) ⁻¹
      ; retractionIso = (FunctorOverIso.underlying Back.left-inverse) ⁻¹ }
  module Changed = Transport p′ new-target f Back.inverse backward-isEquiv Pulled.dependent-product

  dependent-product : DependentProduct p′ f
  dependent-product = Changed.dependent-product
```
