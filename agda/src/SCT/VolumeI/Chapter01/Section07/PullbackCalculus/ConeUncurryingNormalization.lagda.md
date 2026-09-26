# Uncurrying a restricted cone

Restriction of a cone commutes with uncurrying. The matching comparison
uses the postcomposition substitution law and the naturality of uncurrying
on isomorphisms, including the inverse and associativity comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ hiding (funUncurryIso-comp; funUncurryIso-inverse; funUncurry-restrict-inputs)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ

open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingProofs 𝒯 M ℱ

open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

endpoints-iterated : {C D : CAT} {u v u′ v′ u″ v″ : MAP C D}
  (p : u =₁ u′) (q : v =₁ v′) (p′ : u′ =₁ u″) (q′ : v′ =₁ v″) (α : u =₁ v) →
  (changeEndpoints p′ q′ (changeEndpoints p q α)) =₂ (changeEndpoints (p′ ∙ p) (q′ ∙ q) α)
endpoints-iterated p q p′ q′ α = isoComp-cong (idIso (q′ ∙ q))
    (isoComp-cong (idIso α) ((inverse-composite p′ p) ⁻¹) ∙ isoComp-assoc-at α (p ⁻¹) (p′ ⁻¹)) ∙
  ((isoComp-assoc-at q′ q ((α ∙ p ⁻¹) ∙ p′ ⁻¹)) ⁻¹ ∙
    isoComp-cong (idIso q′) (isoComp-assoc-at q (α ∙ p ⁻¹) (p′ ⁻¹)))

module Restriction {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (funPost {C = T} f) (funPost g) X) where

  p = Cone.left s
  q = Cone.right s
  τ = Cone.match s
  F = funPost {C = T} f
  G = funPost {C = T} g
  R = productMap r (id T)
  af = comp-assoc r p F
  ag = comp-assoc r q G
  bf = funUncurry-restrict {C = T} {D = E} (F ∘ p) r
  bg = funUncurry-restrict {C = T} {D = E} (G ∘ q) r
  Ef = funPost-uncurry {C = T} f (p ∘ r) ∙ funUncurryIso {C = T} {D = E} af
  Eg = funPost-uncurry {C = T} g (q ∘ r) ∙ funUncurryIso {C = T} {D = E} ag
  Ef′ = comp-assoc R (funUncurry p) f ∙ (funPost-uncurry {C = T} f p ▷ R)
  Eg′ = comp-assoc R (funUncurry q) g ∙ (funPost-uncurry {C = T} g q ▷ R)
  ℓ = funUncurry-restrict p r
  ρ = funUncurry-restrict q r
  source : Cone f g (Y × T)
  source = uncurryCone {f = f} {g = g} (conePre r s)
  target : Cone f g (Y × T)
  target = conePre R (uncurryCone {f = f} {g = g} s)
  rawSource = changeEndpoints Ef Eg (funUncurryIso {C = T} {D = E} (τ ▷ r))
  rawTarget = changeEndpoints Ef′ Eg′ (funUncurryIso {C = T} {D = E} τ ▷ R)

  abstract
    source-normal : (Cone.match source) =₂ rawSource
    source-normal = endpoints-iterated (funUncurryIso {C = T} {D = E} af) (funUncurryIso {C = T} {D = E} ag)
        (funPost-uncurry {C = T} f (p ∘ r)) (funPost-uncurry {C = T} g (q ∘ r)) (funUncurryIso {C = T} {D = E} (τ ▷ r)) ∙
      isoComp-cong (idIso (funPost-uncurry {C = T} g (q ∘ r)))
        (isoComp-cong
          (isoComp-cong (idIso (funUncurryIso {C = T} {D = E} ag))
            (isoComp-cong (idIso (funUncurryIso {C = T} {D = E} (τ ▷ r))) (funUncurryIso-inverse {C = T} {D = E} af) ∙
              funUncurryIso-comp {C = T} {D = E} (τ ▷ r) (af ⁻¹)) ∙
            funUncurryIso-comp {C = T} {D = E} ag ((τ ▷ r) ∙ af ⁻¹))
          (idIso ((funPost-uncurry {C = T} f (p ∘ r)) ⁻¹)))
  
    target-normal : (Cone.match target) =₂ rawTarget
    target-normal = endpoints-iterated (funPost-uncurry {C = T} f p ▷ R) (funPost-uncurry {C = T} g q ▷ R)
        (comp-assoc R (funUncurry p) f) (comp-assoc R (funUncurry q) g) (funUncurryIso {C = T} {D = E} τ ▷ R) ∙
      isoComp-cong (idIso (comp-assoc R (funUncurry q) g))
        (isoComp-cong
          (isoComp-cong (idIso (funPost-uncurry {C = T} g q ▷ R))
            (isoComp-cong (idIso (funUncurryIso {C = T} {D = E} τ ▷ R)) (pre-inverse (funPost-uncurry {C = T} f p) R) ∙
              preWhisker-isoComp-at (funUncurryIso {C = T} {D = E} τ) ((funPost-uncurry {C = T} f p) ⁻¹) R) ∙
            preWhisker-isoComp-at (funPost-uncurry {C = T} g q) (funUncurryIso {C = T} {D = E} τ ∙ (funPost-uncurry {C = T} f p) ⁻¹) R)
          (idIso ((comp-assoc R (funUncurry p) f) ⁻¹)))
  
```


