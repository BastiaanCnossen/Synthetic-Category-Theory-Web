# Core naming respects identifications

The specified `coreInclusion-name` comparison is natural for the existing
`nameMapIso`. Compare core inclusion with decoding using the same
terminal-product adjustment, then compute the naming action under decoding.

`Roundtrip.At.computation` recovers an identification between named objects
after applying core inclusion and naming again with these endpoint
comparisons. This is a core-naming roundtrip; the relative cone comparisons
still require their separate normalization.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.CoreNamingNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M using (coreInclusion-name)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; left-evaluate; right-evaluate)
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.CoreEvaluationNaturality as Evaluation

module Decoding (C : CAT) where
  adjustment : product-unitʳ-inverse One =₁ oneProduct-in One
  adjustment = pair-cong (terminal-iso _ _) (terminal-iso _ _)

  comparison : (x : Obj-abs (Core C)) → (coreInclusion C ∘ x) =₁ decodeMap x
  comparison x = (mapUncurry x ◁ adjustment) ∙ (core-evaluation x) ⁻¹

  module At {u v : Obj-abs (Core C)} (α : u =₁ v) where
    module E = Evaluation.Naturality 𝒯 M α using (comparison)
    IX = product-unitʳ-inverse One
    raw = mapUncurryIso α

    opaque
      inverse-evaluation : ((core-evaluation v) ⁻¹ ∙ (coreInclusion C ◁ α)) =₂
        ((raw ▷ IX) ∙ (core-evaluation u) ⁻¹)
      inverse-evaluation = move-square (core-evaluation v) (raw ▷ IX)
        (coreInclusion C ◁ α) (core-evaluation u) E.comparison

      naturality : (comparison v ∙ (coreInclusion C ◁ α)) =₂
        (decodeMapIso α ∙ comparison u)
      naturality = isoComp-cong ((decodeMapIso-at α) ⁻¹) (idIso (comparison u)) ∙
        paste-squares ((core-evaluation u) ⁻¹) ((core-evaluation v) ⁻¹)
          (mapUncurry u ◁ adjustment) (mapUncurry v ◁ adjustment)
          (coreInclusion C ◁ α) (raw ▷ IX) (raw ▷ oneProduct-in One)
          inverse-evaluation ((interchange-at raw adjustment) ⁻¹)

module Named {C D : CAT} (u v : MAP C D) (β : u =₁ v) where
  endpoints = leftMultiply ((decode-name v) ⁻¹) ∘ rightMultiply (decode-name u)
  prescribed = endpoints ∘ β
  e = decodeMap-isoMap-isEquiv (nameMap u) (nameMap v)
  chosen = equiv-lift e prescribed

  opaque
    endpoint-computation : prescribed =₂ ((decode-name v) ⁻¹ ∙ (β ∙ decode-name u))
    endpoint-computation =
      isoComp-cong (const-One ((decode-name v) ⁻¹))
        (isoComp-cong (idIso β) (const-One (decode-name u))) ∙
      (left-evaluate ((decode-name v) ⁻¹) (β ∙ const (decode-name u)) ∙
        ((leftMultiply ((decode-name v) ⁻¹) ◁ right-evaluate (decode-name u) β) ∙
          comp-assoc β (rightMultiply (decode-name u)) (leftMultiply ((decode-name v) ⁻¹))))

    image : decodeMapIso (nameMapIso β) =₂ ((decode-name v) ⁻¹ ∙ (β ∙ decode-name u))
    image = endpoint-computation ∙
      (FunctorLift.comparison chosen ∙
        (decodeMap-isoMap (nameMap u) (nameMap v) ◁
          comp-assoc β endpoints (IsEquiv.inverse e)))

    square : (decode-name v ∙ decodeMapIso (nameMapIso β)) =₂ (β ∙ decode-name u)
    square = cancel-inverse (decode-name v) (β ∙ decode-name u) ∙
      isoComp-cong (idIso (decode-name v)) image

module Naturality {C : CAT} (u v : Obj-abs C) (β : u =₁ v) where
  module D = Decoding C using (comparison; module At)
  module N = Named u v β using (square)

  opaque
    comparison : (coreInclusion-name v ∙ (coreInclusion C ◁ nameMapIso β)) =₂
      (β ∙ coreInclusion-name u)
    comparison = paste-squares (D.comparison (nameMap u)) (D.comparison (nameMap v))
      (decode-name u) (decode-name v)
      (coreInclusion C ◁ nameMapIso β) (decodeMapIso (nameMapIso β)) β
      (D.At.naturality (nameMapIso β)) N.square

module Roundtrip {C : CAT} (u v : Obj-abs C) where
  included : (α : nameMap u =₁ nameMap v) → u =₁ v
  included α = coreInclusion-name v ∙
    ((coreInclusion C ◁ α) ∙ (coreInclusion-name u) ⁻¹)

  opaque
    on-image : (β : u =₁ v) → included (nameMapIso β) =₂ β
    on-image β = cancel-right (coreInclusion-name u) β ∙
      (isoComp-cong (Naturality.comparison u v β) (idIso ((coreInclusion-name u) ⁻¹)) ∙
        (isoComp-assoc-at (coreInclusion-name v) (coreInclusion C ◁ nameMapIso β)
          ((coreInclusion-name u) ⁻¹)) ⁻¹)

    congruence : {α β : nameMap u =₁ nameMap v} → α =₂ β → included α =₂ included β
    congruence q = isoComp-cong (idIso (coreInclusion-name v))
      (isoComp-cong (postWhisker (coreInclusion C) ◁ q) (idIso ((coreInclusion-name u) ⁻¹)))

  module At (α : nameMap u =₁ nameMap v) where
    chosen : FunctorLift (nameMap-isoMap u v) α
    chosen = equiv-lift (nameMap-isoMap-isEquiv u v) α
    β = FunctorLift.lift chosen
    image = FunctorLift.comparison chosen

    opaque
      comparison-to-lift : included α =₂ β
      comparison-to-lift = on-image β ∙ congruence (image ⁻¹)

      computation : nameMapIso (included α) =₂ α
      computation = image ∙ nameMap-Iso₂ comparison-to-lift
```
