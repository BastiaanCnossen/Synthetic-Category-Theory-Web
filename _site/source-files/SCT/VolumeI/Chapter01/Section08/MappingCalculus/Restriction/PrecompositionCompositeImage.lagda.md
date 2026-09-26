# The evaluated image of the precomposition compositor

The computation rule for the chosen lift removes the lifted compositor
from the evaluation formula. What remains is a comparison between explicit
product routes. This step uses no anima hypothesis on the parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionCompositeImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (mapUncurry-restrict-inputs)
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
  κ : (mapPre {D = E} f ∘ mapPre g) =₁ (mapPre (g ∘ f))
  κ = mapPre-comp f g
  β = mapPre-β {D = E} (g ∘ f)

  leading : (mapUncurry (mapPre {D = E} f ∘ mapPre g)) =₁ (mapEval ∘ LgfQ)
  leading = (mapEval ◁ productRestriction-comp Q f g) ∙
    (comp-assoc LfQ LgQ mapEval ∙ ((mapPre-β g ▷ LfQ) ∙ mapPre-uncurry f (mapPre g)))
  raw : (mapUncurry (mapPre {D = E} f ∘ mapPre g)) =₁ (mapUncurry (mapPre (g ∘ f)))
  raw = β ⁻¹ ∙ leading

  liftedImage : (mapUncurryIso κ) =₂ raw
  liftedImage = mapReflect-β (map-isAn C E) _ _ raw
  betaSquare : (β ∙ mapUncurryIso κ) =₂ leading
  betaSquare = cancel-inverse β leading ∙ isoComp-cong (idIso β) liftedImage
  restrictedBetaSquare : ((β ▷ HA) ∙ (mapUncurryIso κ ▷ HA)) =₂ (leading ▷ HA)
  restrictedBetaSquare = (preWhisker HA ◁ betaSquare) ∙
    (preWhisker-isoComp-at β (mapUncurryIso κ) HA) ⁻¹

  r₁ = mapUncurry-restrict (mapPre (g ∘ f)) h
  r₂ = β ▷ HA
  r₃ = comp-assoc HA LgfQ mapEval
  r₄ = mapEval ◁ productMap-separate h (g ∘ f)
  r₅ = (comp-assoc LgfX HC mapEval) ⁻¹
  prefix = r₅ ∙ (r₄ ∙ r₃)
  sourceSubstitution = mapUncurry-restrict (mapPre f ∘ mapPre g) h
  action = mapUncurryIso (κ ▷ h)
  restrictedAction = mapUncurryIso κ ▷ HA

  normalize : (mapPre-uncurry (g ∘ f) h) =₂ (prefix ∙ (r₂ ∙ r₁))
  normalize = (isoComp-assoc-at r₅ (r₄ ∙ r₃) (r₂ ∙ r₁)) ⁻¹ ∙
    isoComp-cong (idIso r₅) ((isoComp-assoc-at r₄ r₃ (r₂ ∙ r₁)) ⁻¹)
  restrictionSquare : (r₁ ∙ action) =₂ (restrictedAction ∙ sourceSubstitution)
  restrictionSquare = mapUncurry-restrict-inputs κ h

  abstract
    law : (mapPre-uncurry (g ∘ f) h ∙ mapUncurryIso (mapPre-comp f g ▷ h)) =₂
      (prefix ∙ ((leading ▷ HA) ∙ mapUncurry-restrict (mapPre f ∘ mapPre g) h))
    law = isoComp-cong (idIso prefix)
      (isoComp-cong restrictedBetaSquare (idIso sourceSubstitution)) ∙
      (isoComp-cong (idIso prefix)
        ((isoComp-assoc-at r₂ restrictedAction sourceSubstitution) ⁻¹) ∙
      (isoComp-cong (idIso prefix) (isoComp-cong (idIso r₂) restrictionSquare) ∙
      (isoComp-cong (idIso prefix) (isoComp-assoc-at r₂ r₁ action) ∙
      (isoComp-assoc-at prefix (r₂ ∙ r₁) action ∙ isoComp-cong normalize (idIso action)))))
```
