# Restricting a cone after changing its cospan

Express the cospan action by pasting, changing the left arrow, and
removing a composite. Each of these operations already has a whole-cone
restriction comparison. Their composite supplies restriction for the
specified `CospanMap.mapCone`, including its matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanRestriction
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse; coneIso-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft; changeLeft-pre; changeLeft-iso)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone; compositeConeIso; compositeCone-pre)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks 𝒯 P using (prefix-assoc)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Pasted {C D E C′ D′ E′ X : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (source : Cone f g X) where
  open CospanMap F using (mapCone) renaming (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
  p = Cone.left source
  q = Cone.right source
  σ = Cone.match (mapCone source)
  rightSquare : Cone g′ w D
  rightSquare = record { left = v ; right = g ; match = β }
  rightCone = coneSwap rightSquare
  module Paste = PasteCones f w rightCone
  pasted = Paste.flatten source
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


  value = compositeCone u f′ changed
  abstract
    comparison : ConeIso value (mapCone source)
    comparison = coneIso-compose
      (cone-match-change _ _ _ _ (cancel-right (comp-assoc p u f′) σ))
      (compositeConeIso u f′ changed-comparison)

module Restriction {C D E C′ D′ E′ X Y : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (r : MAP Y X) (s : Cone f g X) where
  open CospanMap F using (mapCone) renaming (left to u; leftSquare to α)
  module Original = Pasted F s using (value; comparison; changed; pasted; module Paste)
  module Restricted = Pasted F (conePre r s) using (value; comparison)
  abstract
    pasted-comparison : ConeIso (conePre r Original.value) Restricted.value
    pasted-comparison = coneIso-compose
      (compositeConeIso u f′ (changeLeft-iso (α ⁻¹) (Original.Paste.flatten-pre r s)))
      (coneIso-compose (compositeConeIso u f′ (changeLeft-pre (α ⁻¹) r Original.pasted))
        (compositeCone-pre u f′ r Original.changed))
    comparison : ConeIso (conePre r (mapCone s)) (mapCone (conePre r s))
    comparison = coneIso-compose Restricted.comparison
      (coneIso-compose pasted-comparison (coneIso-inverse (coneIso-pre r Original.comparison)))
```
