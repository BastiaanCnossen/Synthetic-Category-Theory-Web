# Changing the anima parameter

Currying can be compared before and after a parameter substitution.
The comparison is a lift of the specified beta and uncurrying comparisons;
it does not postulate functoriality of the host currying operation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits

module SCT.VolumeI.Chapter01.Section03.ParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M using (productMap-pair)
open InternalCoherence 𝒯 M using (module RetainedEvaluation)
open Compatibility 𝒯 M using (mapUncurry-pre-inputs)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

mapCurry-pre-image : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (h : MAP (P × C) D) (σ : MAP Q P)
  → NatIso (mapUncurry (mapCurry pAn h ∘ σ))
      (mapUncurry (mapCurry qAn (h ∘ productMap σ (id C))))
mapCurry-pre-image {C = C} pAn qAn h σ =
  invIso (mapCurry-β qAn (h ∘ productMap σ (id C))) ∙
    ((mapCurry-β pAn h ▷ productMap σ (id C)) ∙ mapUncurry-pre (mapCurry pAn h) σ)

mapCurry-pre : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (h : MAP (P × C) D) (σ : MAP Q P)
  → NatIso (mapCurry pAn h ∘ σ) (mapCurry qAn (h ∘ productMap σ (id C)))
mapCurry-pre pAn qAn h σ = mapReflect qAn _ _ (mapCurry-pre-image pAn qAn h σ)

mapCurry-pre-β : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (h : MAP (P × C) D) (σ : MAP Q P)
  → Iso₂ (mapUncurryIso (mapCurry-pre pAn qAn h σ)) (mapCurry-pre-image pAn qAn h σ)
mapCurry-pre-β pAn qAn h σ = mapReflect-β qAn _ _ (mapCurry-pre-image pAn qAn h σ)
```

The image witness of a lifted comparison also controls its restriction.
The following identification relates a restricted lift to a new lift of
its restricted image. Both parameter hypotheses are explicit.

```agda
mapReflect-pre-image : {P Q C D : CAT} (f g : MAP P (Map C D))
  (α : NatIso (mapUncurry f) (mapUncurry g)) (σ : MAP Q P)
  → NatIso (mapUncurry (f ∘ σ)) (mapUncurry (g ∘ σ))
mapReflect-pre-image {C = C} f g α σ = invIso (mapUncurry-pre g σ) ∙
  ((α ▷ productMap σ (id C)) ∙ mapUncurry-pre f σ)

mapReflect-pre : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (f g : MAP P (Map C D)) (α : NatIso (mapUncurry f) (mapUncurry g)) (σ : MAP Q P)
  → Iso₂ (mapReflect pAn f g α ▷ σ)
      (mapReflect qAn (f ∘ σ) (g ∘ σ) (mapReflect-pre-image f g α σ))
mapReflect-pre {C = C} pAn qAn f g α σ =
  let lifted = mapReflect pAn f g α
      restrictedImage = mapUncurryIso (lifted ▷ σ)
      transportedImage = mapReflect-pre-image f g α σ
      restrictionSquare : Iso₂ (mapUncurry-pre g σ ∙ restrictedImage)
        ((α ▷ productMap σ (id C)) ∙ mapUncurry-pre f σ)
      restrictionSquare =
        isoComp-cong (preWhisker (productMap σ (id C)) ◁ mapReflect-β pAn f g α)
          (idIso (mapUncurry-pre f σ)) ∙ mapUncurry-pre-inputs lifted σ
      imageComparison : Iso₂ restrictedImage transportedImage
      imageComparison = isoComp-cong (idIso (invIso (mapUncurry-pre g σ))) restrictionSquare ∙
        invIso (cancel-left (mapUncurry-pre g σ) restrictedImage)
  in mapReflect-Iso₂ qAn (lifted ▷ σ)
      (mapReflect qAn (f ∘ σ) (g ∘ σ) transportedImage)
      (invIso (mapReflect-β qAn (f ∘ σ) (g ∘ σ) transportedImage) ∙ imageComparison)
```

The same control applies when substitution is followed by explicit endpoint
comparisons, as in the book's specialization convention. Inverse
preservation below is derived from the already proved identity and
composition laws.

```agda
mapUncurryIso-inverse : {P C D : CAT} {f g : MAP P (Map C D)} (α : NatIso f g)
  → Iso₂ (mapUncurryIso (invIso α)) (invIso (mapUncurryIso α))
mapUncurryIso-inverse {f = f} α = cancel-right-reflect (mapUncurryIso α)
  (invIso (isoComp-inverseˡ-at (mapUncurryIso α)) ∙
  (mapUncurryIso-id f ∙
  (mapUncurry-Iso₂ (isoComp-inverseˡ-at α) ∙ invIso (mapUncurryIso-comp (invIso α) α))))

mapReflect-pre-image-β : {P Q C D : CAT} (pAn : isAn P)
  (f g : MAP P (Map C D)) (α : NatIso (mapUncurry f) (mapUncurry g)) (σ : MAP Q P)
  → Iso₂ (mapUncurryIso (mapReflect pAn f g α ▷ σ)) (mapReflect-pre-image f g α σ)
mapReflect-pre-image-β {C = C} pAn f g α σ =
  let lifted = mapReflect pAn f g α
      restrictionSquare =
        isoComp-cong (preWhisker (productMap σ (id C)) ◁ mapReflect-β pAn f g α)
          (idIso (mapUncurry-pre f σ)) ∙ mapUncurry-pre-inputs lifted σ
  in isoComp-cong (idIso (invIso (mapUncurry-pre g σ))) restrictionSquare ∙
    invIso (cancel-left (mapUncurry-pre g σ) (mapUncurryIso (lifted ▷ σ)))

mapReflect-specialize-image : {P Q C D : CAT}
  (f g : MAP P (Map C D)) (α : NatIso (mapUncurry f) (mapUncurry g)) (σ : MAP Q P)
  {f′ g′ : MAP Q (Map C D)} → NatIso (f ∘ σ) f′ → NatIso (g ∘ σ) g′
  → NatIso (mapUncurry f′) (mapUncurry g′)
mapReflect-specialize-image f g α σ left right =
  mapUncurryIso right ∙ (mapReflect-pre-image f g α σ ∙ invIso (mapUncurryIso left))

mapReflect-specialize : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (f g : MAP P (Map C D)) (α : NatIso (mapUncurry f) (mapUncurry g)) (σ : MAP Q P)
  {f′ g′ : MAP Q (Map C D)} (left : NatIso (f ∘ σ) f′) (right : NatIso (g ∘ σ) g′)
  → Iso₂ (specialize (mapReflect pAn f g α) σ left right)
      (mapReflect qAn f′ g′ (mapReflect-specialize-image f g α σ left right))
mapReflect-specialize pAn qAn f g α σ {f′} {g′} left right =
  let lifted = mapReflect pAn f g α
      specialized = specialize lifted σ left right
      expectedImage = mapReflect-specialize-image f g α σ left right
      comparison =
        isoComp-cong (idIso (mapUncurryIso right))
          (isoComp-cong (mapReflect-pre-image-β pAn f g α σ) (mapUncurryIso-inverse left)) ∙
        (isoComp-cong (idIso (mapUncurryIso right)) (mapUncurryIso-comp (lifted ▷ σ) (invIso left)) ∙
          mapUncurryIso-comp right ((lifted ▷ σ) ∙ invIso left)) ∙
        mapUncurry-Iso₂ (isoComp-assoc-at right (lifted ▷ σ) (invIso left))
  in mapReflect-Iso₂ qAn specialized (mapReflect qAn f′ g′ expectedImage)
    (invIso (mapReflect-β qAn f′ g′ expectedImage) ∙ comparison)
```

A retained evaluation keeps its parameter as its first coordinate.
Changing the parameter and evaluating can therefore be compared by two
projections. Unlike currying, this construction needs no anima hypothesis.
Its compatibility with multiple substitutions is a further coherence claim.

```agda
retained-parameter-change : {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P)
  → NatIso
      (productMap σ (id D) ∘ RetainedEvaluation.retained Q (f ∘ σ))
      (RetainedEvaluation.retained P f ∘ productMap σ (id C))
retained-parameter-change {P} {Q} {C} {D} f σ =
  let common : MAP (Q × C) (P × D)
      common = pair (σ ∘ pr₁) (mapUncurry f ∘ productMap σ (id C))

      changeThenEvaluate : NatIso
        (productMap σ (id D) ∘ RetainedEvaluation.retained Q (f ∘ σ)) common
      changeThenEvaluate = pair-cong (idIso (σ ∘ pr₁))
        (mapUncurry-pre f σ ∙ comp-unitˡ (mapUncurry (f ∘ σ))) ∙
        productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ))

      evaluateThenChange : NatIso
        (RetainedEvaluation.retained P f ∘ productMap σ (id C)) common
      evaluateThenChange = pair-cong (pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂))
        (idIso (mapUncurry f ∘ productMap σ (id C))) ∙
        pair-pre pr₁ (mapUncurry f) (productMap σ (id C))
  in invIso evaluateThenChange ∙ changeThenEvaluate
```
