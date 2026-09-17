# Equivalences of cospans

For `exercise:Fiber_Product_Of_Equivalences_Is_Equivalence`, paste the
source pullback with the right square of the cospan map. The specified
factorization comparison identifies this rectangle with the rectangle
through the target pullback. Pasting cancellation finishes the proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.CospanEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section05.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
  using (IsPullback; pbCone-isPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section05.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section05.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section05.PastingLemma 𝒯 P using (module Pasting)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

prefix-assoc : {C D : CAT} {f₀ f₁ f₂ f₃ f₄ : MAP C D}
  (a₃ : NatIso f₃ f₄) (a₂ : NatIso f₂ f₃) (a₁ : NatIso f₁ f₂) (a₀ : NatIso f₀ f₁) →
  Iso₂ (a₃ ∙ (a₂ ∙ (a₁ ∙ a₀))) ((a₃ ∙ (a₂ ∙ a₁)) ∙ a₀)
prefix-assoc a₃ a₂ a₁ a₀ = invIso (isoComp-assoc-at a₃ (a₂ ∙ a₁) a₀) ∙
  isoComp-cong (idIso a₃) (invIso (isoComp-assoc-at a₂ a₁ a₀))

module CospanEquivalence {C D E C′ D′ E′ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (eu : IsEquiv (CospanMap.left F))
  (ev : IsEquiv (CospanMap.right F)) (ew : IsEquiv (CospanMap.base F)) where

  open CospanMap F renaming (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
  source = pbCone f g
  target = pbCone f′ g′
  p = Cone.left source
  q = Cone.right source
  H = pullbackMap
  legLeft = ConeIso.leftIso pullbackMap-β
  ρ = ConeIso.rightIso pullbackMap-β
  σ = Cone.match (mapCone source)

  rightSquare : Cone g′ w D
  rightSquare = record { left = v ; right = g ; match = β }
  rightCone = coneSwap rightSquare
  right-isPullback = pullback-swap rightSquare (degenerate-pullback ew rightSquare ev)
  module RightPaste = Pasting f w g′ rightCone right-isPullback
  pasted = RightPaste.Paste.flatten source
  changed = changeLeft (invIso α) pasted

  outerMapped : Cone (f′ ∘ u) g′ (Pullback f g)
  outerMapped = record { left = p ; right = v ∘ q ; match = σ ∙ comp-assoc p u f′ }

  changed-comparison : ConeIso changed outerMapped
  changed-comparison = cone-match-change _ _ _ _
    (invIso normalized ∙
      isoComp-cong (idIso (Cone.match pasted)) (inverse-inverse (α ▷ p) ∙ (isoInv ◁ pre-inverse α p)))
    where
    ar = comp-assoc q v g′
    br = invIso β ▷ q
    cr = invIso (comp-assoc q g w)
    dr = w ◁ Cone.match source
    er = comp-assoc p f w
    fr = α ▷ p
    assocLeft = comp-assoc p u f′
    prefix = ar ∙ (br ∙ cr)
    σ-normal : Iso₂ σ ((Cone.match pasted ∙ fr) ∙ invIso assocLeft)
    σ-normal = invIso (isoComp-assoc-at (Cone.match pasted) fr (invIso assocLeft)) ∙
      (invIso (isoComp-assoc-at prefix (dr ∙ er) (fr ∙ invIso assocLeft)) ∙
      (isoComp-cong (idIso prefix) (invIso (isoComp-assoc-at dr er (fr ∙ invIso assocLeft))) ∙
        prefix-assoc ar br cr (dr ∙ (er ∙ (fr ∙ invIso assocLeft)))))
    normalized : Iso₂ (σ ∙ assocLeft) (Cone.match pasted ∙ fr)
    normalized = isoComp-unitʳ-at (Cone.match pasted ∙ fr) ∙
      (isoComp-cong (idIso (Cone.match pasted ∙ fr)) (isoComp-inverseˡ-at assocLeft) ∙
      (isoComp-assoc-at (Cone.match pasted ∙ fr) (invIso assocLeft) assocLeft ∙
        isoComp-cong σ-normal (idIso assocLeft)))

  outer-isPullback : IsPullback outerMapped
  outer-isPullback = pullback-cone-invariant changed-comparison
    (ChangeLeft.preserve (invIso α) g′ pasted
      (RightPaste.paste-isPullback source (pbCone-isPullback f g)))

  projectionSquare : Cone u (Cone.left target) (Pullback f g)
  projectionSquare = record { left = p ; right = H ; match = invIso legLeft }
  module TargetPaste = Pasting u f′ g′ target (pbCone-isPullback f′ g′)

  outer-comparison : ConeIso (TargetPaste.Paste.flatten projectionSquare) outerMapped
  outer-comparison = compositeCone-compatible u f′ _ _ (idIso p) ρ
    (isoComp-cong (idIso (g′ ◁ ρ)) (invIso (TargetPaste.Paste.flatten-match projectionSquare)) ∙
    (isoComp-assoc-at (g′ ◁ ρ) ν (f′ ◁ invIso legLeft) ∙
    (invIso cancel ∙
    (isoComp-unitʳ-at σ ∙
      isoComp-cong (cancel-right (comp-assoc p u f′) σ)
        (postWhisker-idIso f′ (u ∘ p) ∙ (postWhisker f′ ◁ postWhisker-idIso u p))))))
    where
    ν = Cone.match (conePre H target)
    inverseImage = postWhisker-idIso f′ (u ∘ p) ∙
      ((postWhisker f′ ◁ isoComp-inverseʳ-at legLeft) ∙ invIso (postWhisker-isoComp-at f′ legLeft (invIso legLeft)))
    cancel : Iso₂ (((g′ ◁ ρ) ∙ ν) ∙ (f′ ◁ invIso legLeft)) σ
    cancel = isoComp-unitʳ-at σ ∙
      (isoComp-cong (idIso σ) inverseImage ∙
      (isoComp-assoc-at σ (f′ ◁ legLeft) (f′ ◁ invIso legLeft) ∙
        isoComp-cong (invIso (ConeIso.compatible pullbackMap-β)) (idIso (f′ ◁ invIso legLeft))))

  pullbackMap-isEquiv : IsEquiv pullbackMap
  pullbackMap-isEquiv = degenerate-pullback-converse eu (coneSwap projectionSquare)
    (pullback-swap projectionSquare (TargetPaste.cancel-isPullback projectionSquare
      (pullback-cone-invariant (coneIso-inverse outer-comparison) outer-isPullback)))
```
