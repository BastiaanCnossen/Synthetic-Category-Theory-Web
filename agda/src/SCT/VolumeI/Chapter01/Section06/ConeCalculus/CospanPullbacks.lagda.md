# Mapping a specified pullback cone

A map of cospans with an equivalence on the left and a cartesian right
square sends any specified pullback cone to a pullback cone. The proof
retains the matching produced by `CospanMap.mapCone`: paste with the
right square, change the left arrow, and cancel the target pullback.
`Specified` accepts any target pullback and a map with its whole-cone
comparison; `Mapped` specializes this to the chosen pullback, preserving
its existing factorization map and computation rule.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullbackCone-isPullback; pullback-cone-invariant; pullback-restrict-equivalence)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

prefix-assoc : {C D : CAT} {f₀ f₁ f₂ f₃ f₄ : MAP C D}
  (a₃ : f₃ =₁ f₄) (a₂ : f₂ =₁ f₃) (a₁ : f₁ =₁ f₂) (a₀ : f₀ =₁ f₁) →
  (a₃ ∙ (a₂ ∙ (a₁ ∙ a₀))) =₂ ((a₃ ∙ (a₂ ∙ a₁)) ∙ a₀)
prefix-assoc a₃ a₂ a₁ a₀ = (isoComp-assoc-at a₃ (a₂ ∙ a₁) a₀) ⁻¹ ∙
  isoComp-cong (idIso a₃) ((isoComp-assoc-at a₂ a₁ a₀) ⁻¹)

rightSquareOf : {C D E C′ D′ E′ : CAT} {f : MAP C E} {g : MAP D E}
  {f′ : MAP C′ E′} {g′ : MAP D′ E′} (F : CospanMap f g f′ g′) →
  Cone g′ (CospanMap.base F) D
rightSquareOf F = record { left = CospanMap.right F ; right = _ ; match = CospanMap.rightSquare F }

module Specified {C D E C′ D′ E′ X Y : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′)
  (right-pullback : IsPullback (rightSquareOf F))
  (source : Cone f g X) (source-isPullback : IsPullback source)
  (target : Cone f′ g′ Y) (target-isPullback : IsPullback target)
  (H : MAP X Y) (pullbackMap-β : ConeIso (conePre H target) (CospanMap.mapCone F source)) where

  open CospanMap F using (mapCone) renaming (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
  p = Cone.left source
  q = Cone.right source
  legLeft = ConeIso.leftIso pullbackMap-β
  ρ = ConeIso.rightIso pullbackMap-β
  σ = Cone.match (mapCone source)

  rightSquare : Cone g′ w D
  rightSquare = record { left = v ; right = g ; match = β }
  rightCone = coneSwap rightSquare
  right-isPullback = pullback-swap rightSquare right-pullback
  module RightPaste = Pasting f w g′ rightCone right-isPullback
  pasted = RightPaste.Paste.flatten source
  changed = changeLeft (α ⁻¹) pasted

  outerMapped : Cone (f′ ∘ u) g′ X
  outerMapped = record { left = p ; right = v ∘ q ; match = σ ∙ comp-assoc p u f′ }

  changed-comparison : ConeIso changed outerMapped
  changed-comparison = cone-match-change _ _ _ _
    (normalized ⁻¹ ∙
      isoComp-cong (idIso (Cone.match pasted)) (inverse-inverse (α ▷ p) ∙ (＝-inv ◁ pre-inverse α p)))
    where
    ar = comp-assoc q v g′
    br = β ⁻¹ ▷ q
    cr = (comp-assoc q g w) ⁻¹
    dr = w ◁ Cone.match source
    er = comp-assoc p f w
    fr = α ▷ p
    assocLeft = comp-assoc p u f′
    prefix = ar ∙ (br ∙ cr)
    σ-normal : σ =₂ ((Cone.match pasted ∙ fr) ∙ assocLeft ⁻¹)
    σ-normal = (isoComp-assoc-at (Cone.match pasted) fr (assocLeft ⁻¹)) ⁻¹ ∙
      ((isoComp-assoc-at prefix (dr ∙ er) (fr ∙ assocLeft ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso prefix) ((isoComp-assoc-at dr er (fr ∙ assocLeft ⁻¹)) ⁻¹) ∙
        prefix-assoc ar br cr (dr ∙ (er ∙ (fr ∙ assocLeft ⁻¹)))))
    normalized : (σ ∙ assocLeft) =₂ (Cone.match pasted ∙ fr)
    normalized = isoComp-unitʳ-at (Cone.match pasted ∙ fr) ∙
      (isoComp-cong (idIso (Cone.match pasted ∙ fr)) (isoComp-inverseˡ-at assocLeft) ∙
      (isoComp-assoc-at (Cone.match pasted ∙ fr) (assocLeft ⁻¹) assocLeft ∙
        isoComp-cong σ-normal (idIso assocLeft)))

  outer-isPullback : IsPullback outerMapped
  outer-isPullback = pullback-cone-invariant changed-comparison
    (ChangeLeft.preserve (α ⁻¹) g′ pasted
      (RightPaste.paste-isPullback source source-isPullback))

  projectionSquare : Cone u (Cone.left target) X
  projectionSquare = record { left = p ; right = H ; match = legLeft ⁻¹ }
  module TargetPaste = Pasting u f′ g′ target target-isPullback

  outer-comparison : ConeIso (TargetPaste.Paste.flatten projectionSquare) outerMapped
  outer-comparison = compositeCone-compatible u f′ _ _ (idIso p) ρ
    (isoComp-cong (idIso (g′ ◁ ρ)) ((TargetPaste.Paste.flatten-match projectionSquare) ⁻¹) ∙
    (isoComp-assoc-at (g′ ◁ ρ) ν (f′ ◁ legLeft ⁻¹) ∙
    (cancel ⁻¹ ∙
    (isoComp-unitʳ-at σ ∙
      isoComp-cong (cancel-right (comp-assoc p u f′) σ)
        (postWhisker-idIso f′ (u ∘ p) ∙ (postWhisker f′ ◁ postWhisker-idIso u p))))))
    where
    ν = Cone.match (conePre H target)
    inverseImage = postWhisker-idIso f′ (u ∘ p) ∙
      ((postWhisker f′ ◁ isoComp-inverseʳ-at legLeft) ∙ (postWhisker-isoComp-at f′ legLeft (legLeft ⁻¹)) ⁻¹)
    cancel : (((g′ ◁ ρ) ∙ ν) ∙ (f′ ◁ legLeft ⁻¹)) =₂ σ
    cancel = isoComp-unitʳ-at σ ∙
      (isoComp-cong (idIso σ) inverseImage ∙
      (isoComp-assoc-at σ (f′ ◁ legLeft) (f′ ◁ legLeft ⁻¹) ∙
        isoComp-cong ((ConeIso.compatible pullbackMap-β) ⁻¹) (idIso (f′ ◁ legLeft ⁻¹))))

  projection-square-isPullback : IsPullback projectionSquare
  projection-square-isPullback = TargetPaste.cancel-isPullback projectionSquare
    (pullback-cone-invariant (coneIso-inverse outer-comparison) outer-isPullback)


  abstract
    isPullback : IsEquiv u → IsPullback (mapCone source)
    isPullback eu = pullback-cone-invariant pullbackMap-β
      (pullback-restrict-equivalence target H target-isPullback
        (degenerate-pullback-converse eu (coneSwap projectionSquare)
          (pullback-swap projectionSquare projection-square-isPullback)))

module Mapped {C D E C′ D′ E′ X : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′)
  (right-pullback : IsPullback (rightSquareOf F))
  (source : Cone f g X) (source-isPullback : IsPullback source) where
  target = pullbackCone f′ g′
  H = pullbackLift (CospanMap.mapCone F source)
  pullbackMap-β = pullbackLift-β (CospanMap.mapCone F source)
  open Specified F right-pullback source source-isPullback
    target (pullbackCone-isPullback f′ g′) H pullbackMap-β public
```
