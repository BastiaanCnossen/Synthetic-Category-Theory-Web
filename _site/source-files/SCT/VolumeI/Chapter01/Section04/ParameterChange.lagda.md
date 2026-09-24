# Changing the anima parameter

Currying can be compared before and after a parameter substitution.
The comparison is a lift of the specified beta and uncurrying comparisons;
it does not postulate functoriality of the host currying operation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PairingUnits

module SCT.VolumeI.Chapter01.Section04.ParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M using (productMap-pair)
open InternalCoherence 𝒯 M using (module RetainedEvaluation)
open Compatibility 𝒯 M using (mapUncurry-restrict-inputs)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

mapCurry-restrict-image : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (h : MAP (P × C) D) (σ : MAP Q P)
  → (mapUncurry (mapCurry pAn h ∘ σ)) =₁
      (mapUncurry (mapCurry qAn (h ∘ productMap σ (id C))))
mapCurry-restrict-image {C = C} pAn qAn h σ =
  (mapCurry-β qAn (h ∘ productMap σ (id C))) ⁻¹ ∙
    ((mapCurry-β pAn h ▷ productMap σ (id C)) ∙ mapUncurry-restrict (mapCurry pAn h) σ)

mapCurry-restrict : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (h : MAP (P × C) D) (σ : MAP Q P)
  → (mapCurry pAn h ∘ σ) =₁ (mapCurry qAn (h ∘ productMap σ (id C)))
mapCurry-restrict pAn qAn h σ = mapReflect qAn _ _ (mapCurry-restrict-image pAn qAn h σ)

mapCurry-restrict-β : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (h : MAP (P × C) D) (σ : MAP Q P)
  → (mapUncurryIso (mapCurry-restrict pAn qAn h σ)) =₂ (mapCurry-restrict-image pAn qAn h σ)
mapCurry-restrict-β pAn qAn h σ = mapReflect-β qAn _ _ (mapCurry-restrict-image pAn qAn h σ)
```

The image witness of a lifted comparison also controls its restriction.
The following identification relates a restricted lift to a new lift of
its restricted image. Both parameter hypotheses are explicit.

```agda
mapReflect-pre-image : {P Q C D : CAT} (f g : MAP P (Map C D))
  (α : (mapUncurry f) =₁ (mapUncurry g)) (σ : MAP Q P)
  → (mapUncurry (f ∘ σ)) =₁ (mapUncurry (g ∘ σ))
mapReflect-pre-image {C = C} f g α σ = (mapUncurry-restrict g σ) ⁻¹ ∙
  ((α ▷ productMap σ (id C)) ∙ mapUncurry-restrict f σ)

mapReflect-pre : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (f g : MAP P (Map C D)) (α : (mapUncurry f) =₁ (mapUncurry g)) (σ : MAP Q P)
  → (mapReflect pAn f g α ▷ σ) =₂
      (mapReflect qAn (f ∘ σ) (g ∘ σ) (mapReflect-pre-image f g α σ))
mapReflect-pre {C = C} pAn qAn f g α σ =
  let lifted = mapReflect pAn f g α
      restrictedImage = mapUncurryIso (lifted ▷ σ)
      transportedImage = mapReflect-pre-image f g α σ
      restrictionSquare : (mapUncurry-restrict g σ ∙ restrictedImage) =₂
        ((α ▷ productMap σ (id C)) ∙ mapUncurry-restrict f σ)
      restrictionSquare =
        isoComp-cong (preWhisker (productMap σ (id C)) ◁ mapReflect-β pAn f g α)
          (idIso (mapUncurry-restrict f σ)) ∙ mapUncurry-restrict-inputs lifted σ
      imageComparison : restrictedImage =₂ transportedImage
      imageComparison = isoComp-cong (idIso ((mapUncurry-restrict g σ) ⁻¹)) restrictionSquare ∙
        (cancel-left (mapUncurry-restrict g σ) restrictedImage) ⁻¹
  in mapReflect-Iso₂ qAn (lifted ▷ σ)
      (mapReflect qAn (f ∘ σ) (g ∘ σ) transportedImage)
      ((mapReflect-β qAn (f ∘ σ) (g ∘ σ) transportedImage) ⁻¹ ∙ imageComparison)
```

The same control applies when substitution is followed by explicit endpoint
comparisons, as in the book's specialization convention. Inverse
preservation below is derived from the already proved identity and
composition laws.

```agda
mapUncurryIso-inverse : {P C D : CAT} {f g : MAP P (Map C D)} (α : f =₁ g)
  → (mapUncurryIso (α ⁻¹)) =₂ ((mapUncurryIso α) ⁻¹)
mapUncurryIso-inverse {f = f} α = cancel-right-reflect (mapUncurryIso α)
  ((isoComp-inverseˡ-at (mapUncurryIso α)) ⁻¹ ∙
  (mapUncurryIso-id f ∙
  (mapUncurry-Iso₂ (isoComp-inverseˡ-at α) ∙ (mapUncurryIso-comp (α ⁻¹) α) ⁻¹)))

mapReflect-pre-image-β : {P Q C D : CAT} (pAn : isAn P)
  (f g : MAP P (Map C D)) (α : (mapUncurry f) =₁ (mapUncurry g)) (σ : MAP Q P)
  → (mapUncurryIso (mapReflect pAn f g α ▷ σ)) =₂ (mapReflect-pre-image f g α σ)
mapReflect-pre-image-β {C = C} pAn f g α σ =
  let lifted = mapReflect pAn f g α
      restrictionSquare =
        isoComp-cong (preWhisker (productMap σ (id C)) ◁ mapReflect-β pAn f g α)
          (idIso (mapUncurry-restrict f σ)) ∙ mapUncurry-restrict-inputs lifted σ
  in isoComp-cong (idIso ((mapUncurry-restrict g σ) ⁻¹)) restrictionSquare ∙
    (cancel-left (mapUncurry-restrict g σ) (mapUncurryIso (lifted ▷ σ))) ⁻¹

mapReflect-specialize-image : {P Q C D : CAT}
  (f g : MAP P (Map C D)) (α : (mapUncurry f) =₁ (mapUncurry g)) (σ : MAP Q P)
  {f′ g′ : MAP Q (Map C D)} → (f ∘ σ) =₁ f′ → (g ∘ σ) =₁ g′
  → (mapUncurry f′) =₁ (mapUncurry g′)
mapReflect-specialize-image f g α σ left right =
  mapUncurryIso right ∙ (mapReflect-pre-image f g α σ ∙ (mapUncurryIso left) ⁻¹)

mapReflect-specialize : {P Q C D : CAT} (pAn : isAn P) (qAn : isAn Q)
  (f g : MAP P (Map C D)) (α : (mapUncurry f) =₁ (mapUncurry g)) (σ : MAP Q P)
  {f′ g′ : MAP Q (Map C D)} (left : (f ∘ σ) =₁ f′) (right : (g ∘ σ) =₁ g′)
  → (specialize (mapReflect pAn f g α) σ left right) =₂
      (mapReflect qAn f′ g′ (mapReflect-specialize-image f g α σ left right))
mapReflect-specialize pAn qAn f g α σ {f′} {g′} left right =
  let lifted = mapReflect pAn f g α
      specialized = specialize lifted σ left right
      expectedImage = mapReflect-specialize-image f g α σ left right
      comparison =
        isoComp-cong (idIso (mapUncurryIso right))
          (isoComp-cong (mapReflect-pre-image-β pAn f g α σ) (mapUncurryIso-inverse left)) ∙
        (isoComp-cong (idIso (mapUncurryIso right)) (mapUncurryIso-comp (lifted ▷ σ) (left ⁻¹)) ∙
          mapUncurryIso-comp right ((lifted ▷ σ) ∙ left ⁻¹)) ∙
        mapUncurry-Iso₂ (isoComp-assoc-at right (lifted ▷ σ) (left ⁻¹))
  in mapReflect-Iso₂ qAn specialized (mapReflect qAn f′ g′ expectedImage)
    ((mapReflect-β qAn f′ g′ expectedImage) ⁻¹ ∙ comparison)
```

A retained evaluation keeps its parameter as its first coordinate.
Changing the parameter and evaluating can therefore be compared by two
projections. Unlike currying, this construction needs no anima hypothesis.
Its compatibility with multiple substitutions is a further coherence claim.

```agda
retained-parameter-change : {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P)
  →
      (productMap σ (id D) ∘ RetainedEvaluation.retained Q (f ∘ σ)) =₁
      (RetainedEvaluation.retained P f ∘ productMap σ (id C))
retained-parameter-change {P} {Q} {C} {D} f σ =
  let common : MAP (Q × C) (P × D)
      common = pair (σ ∘ pr₁) (mapUncurry f ∘ productMap σ (id C))

      changeThenEvaluate :
        (productMap σ (id D) ∘ RetainedEvaluation.retained Q (f ∘ σ)) =₁ common
      changeThenEvaluate = pair-cong (idIso (σ ∘ pr₁))
        (mapUncurry-restrict f σ ∙ comp-unitˡ (mapUncurry (f ∘ σ))) ∙
        productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ))

      evaluateThenChange :
        (RetainedEvaluation.retained P f ∘ productMap σ (id C)) =₁ common
      evaluateThenChange = pair-cong (pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂))
        (idIso (mapUncurry f ∘ productMap σ (id C))) ∙
        pair-pre pr₁ (mapUncurry f) (productMap σ (id C))
  in evaluateThenChange ⁻¹ ∙ changeThenEvaluate
```
