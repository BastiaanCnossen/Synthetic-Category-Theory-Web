# Transferring pullback pasting to mapping squares

Mapping out reverses the order of the two squares. Once the matching of
the pasted mapping square is compared with the mapping of the specified
outer square, the pullback pasting lemma gives both directions. This
intermediate module accepts a full cone comparison. A stronger entry point
also accepts the matching identity with the displayed compositor legs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PastingTransfer
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Diagram {A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
  {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃}
  {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
  {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
  (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂) where

  outer = PastedSquare.outer left right

  module At (E : CAT) where
    t = mappingOut left E
    s = mappingOut right E
    module Paste = PasteCones (mapPre {D = E} g₂) (mapPre g₁) t
    flat = Paste.flatten s
    mappedOuter = mappingOut outer E
    κg = mapPre-comp {D = E} g₁ g₂
    κh = mapPre-comp {D = E} h₁ h₂
    change = κg ▷ mapPre f₃
    rightChange = mapPre f₁ ◁ κh

    MatchingComparison : Set m
    MatchingComparison = (Cone.match mappedOuter ∙ change) =₂
      (rightChange ∙ Cone.match flat)

    module WithComparison (comparison : ConeIso (changeLeft κg flat) mappedOuter) where
      module Change = ChangeLeft κg (mapPre f₁)

      paste : IsPullback t → IsPullback s → IsPullback mappedOuter
      paste et es = pullback-cone-invariant comparison
        (Change.preserve flat (Pasting.paste-isPullback (mapPre g₂) (mapPre g₁) (mapPre f₁) t et s es))

      cancel : IsPullback t → IsPullback mappedOuter → IsPullback s
      cancel et eo = Pasting.cancel-isPullback (mapPre g₂) (mapPre g₁) (mapPre f₁) t et s
        (Change.reflect flat (pullback-cone-invariant (coneIso-inverse comparison) eo))


    module WithMatching (matching : MatchingComparison) where
      comparison : ConeIso (changeLeft κg flat) mappedOuter
      comparison = record
        { leftIso = idIso (mapPre f₃) ; rightIso = κh
        ; compatible = isoComp-assoc-at rightChange (Cone.match flat) (change ⁻¹) ∙
            (isoComp-cong matching (idIso (change ⁻¹)) ∙
            ((cancel-right change (Cone.match mappedOuter)) ⁻¹ ∙
            (isoComp-unitʳ-at (Cone.match mappedOuter) ∙
              isoComp-cong (idIso (Cone.match mappedOuter))
                (postWhisker-idIso (mapPre (g₂ ∘ g₁)) (mapPre f₃))))) }

      open WithComparison comparison public using (paste; cancel)

  module WithMatchings (matching : (E : CAT) → At.MatchingComparison E) where
    paste : IsPushout left → IsPushout right → IsPushout outer
    paste el er E = At.WithMatching.paste E (matching E) (el E) (er E)

    cancel : IsPushout left → IsPushout outer → IsPushout right
    cancel el eo E = At.WithMatching.cancel E (matching E) (el E) (eo E)
```
