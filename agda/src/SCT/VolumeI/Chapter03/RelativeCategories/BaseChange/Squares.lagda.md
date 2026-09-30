# The cartesian square of native base change

Base change of a functor over the base is cartesian over its underlying
functor. Paste its projection square with the target pullback. The
outer square is the source pullback with its left arrow changed by the
specified triangle. Cancellation proves the assertion, retaining the
actual beta comparison of the base-change cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Squares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullbackCone-isPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Cartesian {C D S T : CAT} {f : MAP C T} {g : MAP D T}
  (p : MAP S T) (u : FunctorOver f g) where
  h = FunctorLift.lift u
  θ = FunctorLift.comparison u
  source = pullbackCone f p
  target = pullbackCone g p
  acted = Change.cone p u
  H = pullbackLift acted
  β = pullbackLift-β acted
  first = ConeIso.leftIso β
  second = ConeIso.rightIso β
  r = Cone.left source
  q = Cone.right source
  A = comp-assoc r h g
  σ = Cone.match acted
  changed = changeLeft (θ ⁻¹) source
  outer : Cone (g ∘ h) p (Pullback f p)
  outer = record { left = r ; right = q ; match = σ ∙ A }

  abstract
    normal : (σ ∙ A) =₂ (Cone.match source ∙ (θ ▷ r))
    normal = isoComp-unitʳ-at (Cone.match source ∙ (θ ▷ r)) ∙
      (isoComp-cong (idIso (Cone.match source ∙ (θ ▷ r))) (isoComp-inverseˡ-at A) ∙
        (isoComp-assoc-at (Cone.match source ∙ (θ ▷ r)) (A ⁻¹) A ∙
          isoComp-cong ((isoComp-assoc-at (Cone.match source) (θ ▷ r) (A ⁻¹)) ⁻¹) (idIso A)))
    change-comparison : ConeIso changed outer
    change-comparison = cone-match-change _ _ _ _ (normal ⁻¹ ∙
      isoComp-cong (idIso (Cone.match source))
        (inverse-inverse (θ ▷ r) ∙ (＝-inv ◁ pre-inverse θ r)))
    outer-isPullback : IsPullback outer
    outer-isPullback = pullback-cone-invariant change-comparison
      (ChangeLeft.preserve (θ ⁻¹) p source (pullbackCone-isPullback f p))

  square : Cone h (Cone.left target) (Pullback f p)
  square = record { left = r ; right = H ; match = first ⁻¹ }
  module Paste = Pasting h g p target (pullbackCone-isPullback g p)
  ν = Cone.match (conePre H target)

  abstract
    cancel : (((p ◁ second) ∙ ν) ∙ (g ◁ first ⁻¹)) =₂ σ
    cancel = isoComp-unitʳ-at σ ∙
      (isoComp-cong (idIso σ)
        (postWhisker-idIso g (h ∘ r) ∙
          ((postWhisker g ◁ isoComp-inverseʳ-at first) ∙
            (postWhisker-isoComp-at g first (first ⁻¹)) ⁻¹)) ∙
        (isoComp-assoc-at σ (g ◁ first) (g ◁ first ⁻¹) ∙
          isoComp-cong ((ConeIso.compatible β) ⁻¹) (idIso (g ◁ first ⁻¹))))
    outer-comparison : ConeIso (Paste.Paste.flatten square) outer
    outer-comparison = compositeCone-compatible h g _ _ (idIso r) second
      (isoComp-cong (idIso (p ◁ second)) ((Paste.Paste.flatten-match square) ⁻¹) ∙
        (isoComp-assoc-at (p ◁ second) ν (g ◁ first ⁻¹) ∙
          (cancel ⁻¹ ∙
            (isoComp-unitʳ-at σ ∙
              isoComp-cong (cancel-right A σ)
                (postWhisker-idIso g (h ∘ r) ∙
                  (postWhisker g ◁ postWhisker-idIso h r))))))
    square-isPullback : IsPullback square
    square-isPullback = Paste.cancel-isPullback square
      (pullback-cone-invariant (coneIso-inverse outer-comparison) outer-isPullback)
```
