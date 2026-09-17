# The evaluated image of the precomposition compositor

The computation rule for the chosen lift removes the lifted compositor
from the evaluation formula. What remains is a comparison between explicit
product routes. This step uses no anima hypothesis on the parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.PrecompositionCompositeImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M using (mapUncurry-pre-inputs)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module CompositorImage {X A B C E : CAT}
  (f : MAP A B) (g : MAP B C) (h : MAP X (Map C E)) where

  Q = Map C E
  HA = productMap h (id A)
  HC = productMap h (id C)
  LfQ = productMap (id Q) f
  LgQ = productMap (id Q) g
  LgfQ = productMap (id Q) (g ∘ f)
  LgfX = productMap (id X) (g ∘ f)
  κ : NatIso (mapPre {D = E} f ∘ mapPre g) (mapPre (g ∘ f))
  κ = mapPre-comp f g
  β = mapPre-β {D = E} (g ∘ f)

  leading : NatIso (mapUncurry (mapPre {D = E} f ∘ mapPre g)) (mapEval ∘ LgfQ)
  leading = (mapEval ◁ productRestriction-comp Q f g) ∙
    (comp-assoc LfQ LgQ mapEval ∙ ((mapPre-β g ▷ LfQ) ∙ mapPre-uncurry f (mapPre g)))
  raw : NatIso (mapUncurry (mapPre {D = E} f ∘ mapPre g)) (mapUncurry (mapPre (g ∘ f)))
  raw = invIso β ∙ leading

  liftedImage : Iso₂ (mapUncurryIso κ) raw
  liftedImage = mapReflect-β (map-isAn C E) _ _ raw
  betaSquare : Iso₂ (β ∙ mapUncurryIso κ) leading
  betaSquare = cancel-inverse β leading ∙ isoComp-cong (idIso β) liftedImage
  restrictedBetaSquare : Iso₂ ((β ▷ HA) ∙ (mapUncurryIso κ ▷ HA)) (leading ▷ HA)
  restrictedBetaSquare = (preWhisker HA ◁ betaSquare) ∙
    invIso (preWhisker-isoComp-at β (mapUncurryIso κ) HA)

  r₁ = mapUncurry-pre (mapPre (g ∘ f)) h
  r₂ = β ▷ HA
  r₃ = comp-assoc HA LgfQ mapEval
  r₄ = mapEval ◁ productMap-separate h (g ∘ f)
  r₅ = invIso (comp-assoc LgfX HC mapEval)
  prefix = r₅ ∙ (r₄ ∙ r₃)
  sourceSubstitution = mapUncurry-pre (mapPre f ∘ mapPre g) h
  action = mapUncurryIso (κ ▷ h)
  restrictedAction = mapUncurryIso κ ▷ HA

  normalize : Iso₂ (mapPre-uncurry (g ∘ f) h) (prefix ∙ (r₂ ∙ r₁))
  normalize = invIso (isoComp-assoc-at r₅ (r₄ ∙ r₃) (r₂ ∙ r₁)) ∙
    isoComp-cong (idIso r₅) (invIso (isoComp-assoc-at r₄ r₃ (r₂ ∙ r₁)))
  restrictionSquare : Iso₂ (r₁ ∙ action) (restrictedAction ∙ sourceSubstitution)
  restrictionSquare = mapUncurry-pre-inputs κ h

  abstract
    law : Iso₂ (mapPre-uncurry (g ∘ f) h ∙ mapUncurryIso (mapPre-comp f g ▷ h))
      (prefix ∙ ((leading ▷ HA) ∙ mapUncurry-pre (mapPre f ∘ mapPre g) h))
    law = isoComp-cong (idIso prefix)
      (isoComp-cong restrictedBetaSquare (idIso sourceSubstitution)) ∙
      (isoComp-cong (idIso prefix)
        (invIso (isoComp-assoc-at r₂ restrictedAction sourceSubstitution)) ∙
      (isoComp-cong (idIso prefix) (isoComp-cong (idIso r₂) restrictionSquare) ∙
      (isoComp-cong (idIso prefix) (isoComp-assoc-at r₂ r₁ action) ∙
      (isoComp-assoc-at prefix (r₂ ∙ r₁) action ∙ isoComp-cong normalize (idIso action)))))
```
