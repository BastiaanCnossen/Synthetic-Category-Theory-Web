# Uncurrying cones and their comparisons

Uncurrying a cone transports its matching isomorphism by the two
postcomposition comparisons. Naturality and preservation of composition
then uncurry the compatibility square of a cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.ConeUncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.MappingCompatibility 𝒯 M ℱ
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

paste-iso-squares : {C D : CAT} {x₀ x₁ y₀ y₁ z₀ z₁ : MAP C D}
  (u₀ : =₁ x₀ y₀) (u₁ : =₁ x₁ y₁) (v₀ : =₁ y₀ z₀) (v₁ : =₁ y₁ z₁)
  (α : =₁ x₀ x₁) (β : =₁ y₀ y₁) (γ : =₁ z₀ z₁) →
  =₂ (u₁ ∙ α) (β ∙ u₀) → =₂ (v₁ ∙ β) (γ ∙ v₀) →
  =₂ ((v₁ ∙ u₁) ∙ α) (γ ∙ (v₀ ∙ u₀))
paste-iso-squares u₀ u₁ v₀ v₁ α β γ p q = isoComp-assoc-at γ v₀ u₀ ∙
  (isoComp-cong q (idIso u₀) ∙
  (invIso (isoComp-assoc-at v₁ β u₀) ∙
  (isoComp-cong (idIso v₁) p ∙ isoComp-assoc-at v₁ u₁ α)))

uncurryCone : {X T C D E : CAT} {f : MAP C E} {g : MAP D E} →
  Cone (funPost {C = T} f) (funPost g) X → Cone f g (X × T)
uncurryCone {f = f} {g} s = record
  { left = funUncurry (Cone.left s) ; right = funUncurry (Cone.right s)
  ; match = funPost-uncurry g (Cone.right s) ∙
      (funUncurryIso (Cone.match s) ∙ invIso (funPost-uncurry f (Cone.left s))) }

uncurryConeIso : {X T C D E : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone (funPost {C = T} f) (funPost g) X} → ConeIso s t → ConeIso (uncurryCone s) (uncurryCone t)
uncurryConeIso {f = f} {g} {s} {t} Φ = record
  { leftIso = funUncurryIso α ; rightIso = funUncurryIso β
  ; compatible = paste-iso-squares (τs ∙ invIso fs) (τt ∙ invIso ft) gs gt first third last
      (paste-iso-squares (invIso fs) (invIso ft) τs τt first second third
        (move-square ft second first fs (funPost-uncurry-natural f α)) rawSquare)
      (funPost-uncurry-natural g β) }
  where
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ
  fs = funPost-uncurry f (Cone.left s)
  ft = funPost-uncurry f (Cone.left t)
  gs = funPost-uncurry g (Cone.right s)
  gt = funPost-uncurry g (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)
  first = f ◁ funUncurryIso α
  second = funUncurryIso (funPost f ◁ α)
  third = funUncurryIso (funPost g ◁ β)
  last = g ◁ funUncurryIso β
  rawSquare = funUncurryIso-comp (funPost g ◁ β) (Cone.match s) ∙
    ((funUncurry-isoMap _ _ ◁ ConeIso.compatible Φ) ∙
      invIso (funUncurryIso-comp (Cone.match t) (funPost f ◁ α)))
```

