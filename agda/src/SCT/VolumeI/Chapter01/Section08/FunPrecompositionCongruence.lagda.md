# Evaluating precomposition isomorphisms for functor categories

The same product separation calculation applies to functor-category
uncurrying. We use the chosen `preCong` and its retained computation rule.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.FunPrecompositionCongruence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.PrecompositionCongruence 𝒯 M
  using (productMap-separate-second)
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (post-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; postWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
module CongruenceAt {X A B E : CAT} {f g : MAP A B}
  (α : =₁ f g) (h : MAP X (Fun B E)) where

  γ : =₁ (funPre {D = E} f) (funPre g)
  γ = preCong α
  HA = productMap h (id A)
  HB = productMap h (id B)
  Lf = productMap (id X) f
  Lg = productMap (id X) g
  Kf = productMap (id (Fun B E)) f
  Kg = productMap (id (Fun B E)) g
  smallImage = productMap-cong (idIso (id X)) α
  largeImage = productMap-cong (idIso (id (Fun B E))) α
  βf = funPre-β {D = E} f
  βg = funPre-β {D = E} g
  evaluatedImage = funEval ◁ largeImage

  liftedImage : =₂ (funUncurryIso γ) (invIso βg ∙ (evaluatedImage ∙ βf))
  liftedImage = preCong-β α

  betaSquare : =₂ (βg ∙ funUncurryIso γ) (evaluatedImage ∙ βf)
  betaSquare = cancel-inverse βg (evaluatedImage ∙ βf) ∙
    isoComp-cong (idIso βg) liftedImage

  r₁f = funUncurry-pre (funPre f) h
  r₁g = funUncurry-pre (funPre g) h
  r₂f = βf ▷ HA
  r₂g = βg ▷ HA
  r₃f = comp-assoc HA Kf funEval
  r₃g = comp-assoc HA Kg funEval
  r₄f = funEval ◁ productMap-separate h f
  r₄g = funEval ◁ productMap-separate h g
  r₅f = invIso (comp-assoc Lf HB funEval)
  r₅g = invIso (comp-assoc Lg HB funEval)
  action₀ = funUncurryIso (γ ▷ h)
  action₁ = funUncurryIso γ ▷ HA
  action₂ = evaluatedImage ▷ HA
  action₃ = funEval ◁ (largeImage ▷ HA)
  action₄ = funEval ◁ (HB ◁ smallImage)
  action₅ = funUncurry h ◁ smallImage
  step₁ = funUncurry-pre-inputs γ h
  step₂ = preWhisker-isoComp-at evaluatedImage βf HA ∙
    ((preWhisker HA ◁ betaSquare) ∙
      invIso (preWhisker-isoComp-at βg (funUncurryIso γ) HA))
  step₃ = whisker-mixed-at largeImage HA funEval
  step₄ = post-square funEval (productMap-separate h f) (productMap-separate h g)
    (largeImage ▷ HA) (HB ◁ smallImage) (productMap-separate-second h α)
  step₅ = move-square (comp-assoc Lg HB funEval) action₅ action₄
    (comp-assoc Lf HB funEval) (postWhisker-comp-at smallImage HB funEval)

  abstract
    law : =₂ (funPre-uncurry g h ∙ funUncurryIso (γ ▷ h))
      ((funUncurry h ◁ productMap-cong (idIso (id X)) α) ∙ funPre-uncurry f h)
    law = paste-squares (r₄f ∙ (r₃f ∙ (r₂f ∙ r₁f))) (r₄g ∙ (r₃g ∙ (r₂g ∙ r₁g)))
      r₅f r₅g action₀ action₄ action₅
      (paste-squares (r₃f ∙ (r₂f ∙ r₁f)) (r₃g ∙ (r₂g ∙ r₁g)) r₄f r₄g action₀ action₃ action₄
        (paste-squares (r₂f ∙ r₁f) (r₂g ∙ r₁g) r₃f r₃g action₀ action₂ action₃
          (paste-squares r₁f r₁g r₂f r₂g action₀ action₁ action₂ step₁ step₂) step₃) step₄) step₅

preCong-at : {X A B E : CAT} {f g : MAP A B}
  (α : =₁ f g) (h : MAP X (Fun B E)) →
  =₂ (funPre-uncurry g h ∙ funUncurryIso (preCong α ▷ h))
    ((funUncurry h ◁ productMap-cong (idIso (id X)) α) ∙ funPre-uncurry f h)
preCong-at = CongruenceAt.law
```

