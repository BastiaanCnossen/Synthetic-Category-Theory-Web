# Uncurrying cones and their comparisons

Uncurrying a cone transports its matching isomorphism by the two
postcomposition comparisons. Naturality and preservation of composition
then uncurry the compatibility square of a cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.ConeUncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯 public
open import SCT.VolumeI.Chapter01.Section05.MappingCompatibility 𝒯 M
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
  Cone (mapPost {C = T} f) (mapPost g) X → Cone f g (X × T)
uncurryCone {f = f} {g} s = record
  { left = mapUncurry (Cone.left s) ; right = mapUncurry (Cone.right s)
  ; match = mapPost-uncurry g (Cone.right s) ∙
      (mapUncurryIso (Cone.match s) ∙ invIso (mapPost-uncurry f (Cone.left s))) }

uncurryConeIso : {X T C D E : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone (mapPost {C = T} f) (mapPost g) X} → ConeIso s t → ConeIso (uncurryCone s) (uncurryCone t)
uncurryConeIso {f = f} {g} {s} {t} Φ = record
  { leftIso = mapUncurryIso α ; rightIso = mapUncurryIso β
  ; compatible = paste-iso-squares (τs ∙ invIso fs) (τt ∙ invIso ft) gs gt first third last
      (paste-iso-squares (invIso fs) (invIso ft) τs τt first second third
        (move-square ft second first fs (mapPost-uncurry-natural f α)) rawSquare)
      (mapPost-uncurry-natural g β) }
  where
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ
  fs = mapPost-uncurry f (Cone.left s)
  ft = mapPost-uncurry f (Cone.left t)
  gs = mapPost-uncurry g (Cone.right s)
  gt = mapPost-uncurry g (Cone.right t)
  τs = mapUncurryIso (Cone.match s)
  τt = mapUncurryIso (Cone.match t)
  first = f ◁ mapUncurryIso α
  second = mapUncurryIso (mapPost f ◁ α)
  third = mapUncurryIso (mapPost g ◁ β)
  last = g ◁ mapUncurryIso β
  rawSquare = mapUncurryIso-comp (mapPost g ◁ β) (Cone.match s) ∙
    ((mapUncurry-isoMap _ _ ◁ ConeIso.compatible Φ) ∙
      invIso (mapUncurryIso-comp (Cone.match t) (mapPost f ◁ α)))
```
