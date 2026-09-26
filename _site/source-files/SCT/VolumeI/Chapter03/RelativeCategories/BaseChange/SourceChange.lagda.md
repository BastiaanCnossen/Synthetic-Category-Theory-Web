# Changing a structure functor by an identification

A specified identification between two structure functors induces an
equivalence between the corresponding categories of functors over the
base. Transport the entire defining fiber cone, including its matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.SourceChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameChange 𝒯 M ℱ P using () renaming (module Change to NamedChange)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module Change {C D S : CAT} {f f′ : MAP C S} (α : f =₁ f′) (g : MAP D S) where
  named = NamedChange.named α
  original = pullbackCone (funPost g) (nameFun f)
  transported = changeLeft named (coneSwap original)
  cone = record { left = Cone.left original ; right = Cone.right original
    ; match = (named ▷ Cone.right original) ∙ Cone.match original }

  normalized : ConeIso (coneSwap transported) cone
  normalized = cone-match-change _ _ _ _
    (isoComp-cong (inverse-inverse (named ▷ Cone.right original)) (inverse-inverse (Cone.match original)) ∙
      inverse-composite (Cone.match original ⁻¹) ((named ▷ Cone.right original) ⁻¹))

  cone-isPullback : IsPullback cone
  cone-isPullback = pullback-cone-invariant normalized (pullback-swap transported
    (ChangeLeft.preserve named (funPost g) (coneSwap original)
      (pullback-swap original (pullbackCone-isPullback (funPost g) (nameFun f)))))

  abstract
    functor : MAP (FunOver f g) (FunOver f′ g)
    functor = pullbackLift cone

    functor-isEquiv : IsEquiv functor
    functor-isEquiv = cone-isPullback

    comparison : ConeIso (conePre functor (pullbackCone (funPost g) (nameFun f′))) cone
    comparison = pullbackLift-β cone

  maps : MAP (MapOver f g) (MapOver f′ g)
  maps = mapPost functor

  maps-isEquiv : IsEquiv maps
  maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```
