# The evaluated functor-category precomposition compositor

The computation rule for the chosen lift removes the lifted compositor
from the evaluation formula. What remains is a comparison between explicit
product routes. This step uses no anima hypothesis on the parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositeImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
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
  κ : =₁ (funPre {D = E} f ∘ funPre g) (funPre (g ∘ f))
  κ = preComp f g
  β = funPre-β {D = E} (g ∘ f)

  leading : =₁ (funUncurry (funPre {D = E} f ∘ funPre g)) (funEval ∘ LgfQ)
  leading = (funEval ◁ productRestriction-comp Q f g) ∙
    (comp-assoc LfQ LgQ funEval ∙ ((funPre-β g ▷ LfQ) ∙ funPre-uncurry f (funPre g)))
  raw : =₁ (funUncurry (funPre {D = E} f ∘ funPre g)) (funUncurry (funPre (g ∘ f)))
  raw = invIso β ∙ leading

  liftedImage : =₂ (funUncurryIso κ) raw
  liftedImage = preComp-β f g
  betaSquare : =₂ (β ∙ funUncurryIso κ) leading
  betaSquare = cancel-inverse β leading ∙ isoComp-cong (idIso β) liftedImage
  restrictedBetaSquare : =₂ ((β ▷ HA) ∙ (funUncurryIso κ ▷ HA)) (leading ▷ HA)
  restrictedBetaSquare = (preWhisker HA ◁ betaSquare) ∙
    invIso (preWhisker-isoComp-at β (funUncurryIso κ) HA)

  r₁ = funUncurry-pre (funPre (g ∘ f)) h
  r₂ = β ▷ HA
  r₃ = comp-assoc HA LgfQ funEval
  r₄ = funEval ◁ productMap-separate h (g ∘ f)
  r₅ = invIso (comp-assoc LgfX HC funEval)
  prefix = r₅ ∙ (r₄ ∙ r₃)
  sourceSubstitution = funUncurry-pre (funPre f ∘ funPre g) h
  action = funUncurryIso (κ ▷ h)
  restrictedAction = funUncurryIso κ ▷ HA

  normalize : =₂ (funPre-uncurry (g ∘ f) h) (prefix ∙ (r₂ ∙ r₁))
  normalize = invIso (isoComp-assoc-at r₅ (r₄ ∙ r₃) (r₂ ∙ r₁)) ∙
    isoComp-cong (idIso r₅) (invIso (isoComp-assoc-at r₄ r₃ (r₂ ∙ r₁)))
  restrictionSquare : =₂ (r₁ ∙ action) (restrictedAction ∙ sourceSubstitution)
  restrictionSquare = funUncurry-pre-inputs κ h

  abstract
    law : =₂ (funPre-uncurry (g ∘ f) h ∙ funUncurryIso (preComp f g ▷ h))
      (prefix ∙ ((leading ▷ HA) ∙ funUncurry-pre (funPre f ∘ funPre g) h))
    law = isoComp-cong (idIso prefix)
      (isoComp-cong restrictedBetaSquare (idIso sourceSubstitution)) ∙
      (isoComp-cong (idIso prefix)
        (invIso (isoComp-assoc-at r₂ restrictedAction sourceSubstitution)) ∙
      (isoComp-cong (idIso prefix) (isoComp-cong (idIso r₂) restrictionSquare) ∙
      (isoComp-cong (idIso prefix) (isoComp-assoc-at r₂ r₁ action) ∙
      (isoComp-assoc-at prefix (r₂ ∙ r₁) action ∙ isoComp-cong normalize (idIso action)))))
```
