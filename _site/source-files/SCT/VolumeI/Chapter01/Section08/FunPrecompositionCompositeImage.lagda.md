# The evaluated functor-category precomposition compositor

The computation rule for the chosen lift removes the lifted compositor
from the evaluation formula. What remains is a comparison between explicit
product routes. This step uses no anima hypothesis on the parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositeImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module CompositorImage {X A B C E : CAT}
  (f : MAP A B) (g : MAP B C) (h : MAP X (Fun C E)) where

  Q = Fun C E
  HA = productMap h (id A)
  HC = productMap h (id C)
  LfQ = productMap (id Q) f
  LgQ = productMap (id Q) g
  LgfQ = productMap (id Q) (g ∘ f)
  LgfX = productMap (id X) (g ∘ f)
  κ : (funPre {D = E} f ∘ funPre g) =₁ (funPre (g ∘ f))
  κ = preComp f g
  β = funPre-β {D = E} (g ∘ f)

  leading : (funUncurry (funPre {D = E} f ∘ funPre g)) =₁ (funEval ∘ LgfQ)
  leading = (funEval ◁ productRestriction-comp Q f g) ∙
    (comp-assoc LfQ LgQ funEval ∙ ((funPre-β g ▷ LfQ) ∙ funPre-uncurry f (funPre g)))
  raw : (funUncurry (funPre {D = E} f ∘ funPre g)) =₁ (funUncurry (funPre (g ∘ f)))
  raw = β ⁻¹ ∙ leading

  liftedImage : (funUncurryIso κ) =₂ raw
  liftedImage = preComp-β f g
  betaSquare : (β ∙ funUncurryIso κ) =₂ leading
  betaSquare = cancel-inverse β leading ∙ isoComp-cong (idIso β) liftedImage
  restrictedBetaSquare : ((β ▷ HA) ∙ (funUncurryIso κ ▷ HA)) =₂ (leading ▷ HA)
  restrictedBetaSquare = (preWhisker HA ◁ betaSquare) ∙
    (preWhisker-isoComp-at β (funUncurryIso κ) HA) ⁻¹

  r₁ = funUncurry-restrict (funPre (g ∘ f)) h
  r₂ = β ▷ HA
  r₃ = comp-assoc HA LgfQ funEval
  r₄ = funEval ◁ productMap-separate h (g ∘ f)
  r₅ = (comp-assoc LgfX HC funEval) ⁻¹
  prefix = r₅ ∙ (r₄ ∙ r₃)
  sourceSubstitution = funUncurry-restrict (funPre f ∘ funPre g) h
  action = funUncurryIso (κ ▷ h)
  restrictedAction = funUncurryIso κ ▷ HA

  normalize : (funPre-uncurry (g ∘ f) h) =₂ (prefix ∙ (r₂ ∙ r₁))
  normalize = (isoComp-assoc-at r₅ (r₄ ∙ r₃) (r₂ ∙ r₁)) ⁻¹ ∙
    isoComp-cong (idIso r₅) ((isoComp-assoc-at r₄ r₃ (r₂ ∙ r₁)) ⁻¹)
  restrictionSquare : (r₁ ∙ action) =₂ (restrictedAction ∙ sourceSubstitution)
  restrictionSquare = funUncurry-restrict-inputs κ h

  abstract
    law : (funPre-uncurry (g ∘ f) h ∙ funUncurryIso (preComp f g ▷ h)) =₂
      (prefix ∙ ((leading ▷ HA) ∙ funUncurry-restrict (funPre f ∘ funPre g) h))
    law = isoComp-cong (idIso prefix)
      (isoComp-cong restrictedBetaSquare (idIso sourceSubstitution)) ∙
      (isoComp-cong (idIso prefix)
        ((isoComp-assoc-at r₂ restrictedAction sourceSubstitution) ⁻¹) ∙
      (isoComp-cong (idIso prefix) (isoComp-cong (idIso r₂) restrictionSquare) ∙
      (isoComp-cong (idIso prefix) (isoComp-assoc-at r₂ r₁ action) ∙
      (isoComp-assoc-at prefix (r₂ ∙ r₁) action ∙ isoComp-cong normalize (idIso action)))))
```
