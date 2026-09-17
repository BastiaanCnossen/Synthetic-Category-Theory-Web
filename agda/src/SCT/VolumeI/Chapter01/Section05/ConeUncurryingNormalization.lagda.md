# Uncurrying a restricted cone

Restriction of a cone commutes with uncurrying. The matching comparison
uses the postcomposition substitution law and the naturality of uncurrying
on isomorphisms, including the inverse and associativity comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.ConeUncurryingNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M hiding (mapUncurryIso-comp)
open import SCT.VolumeI.Chapter01.Section05.ConeUncurrying 𝒯 M

open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section05.MappingProofs 𝒯 M

open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯 using (changeEndpoints)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

endpoints-iterated : {C D : CAT} {u v u′ v′ u″ v″ : MAP C D}
  (p : NatIso u u′) (q : NatIso v v′) (p′ : NatIso u′ u″) (q′ : NatIso v′ v″) (α : NatIso u v) →
  Iso₂ (changeEndpoints p′ q′ (changeEndpoints p q α)) (changeEndpoints (p′ ∙ p) (q′ ∙ q) α)
endpoints-iterated p q p′ q′ α = isoComp-cong (idIso (q′ ∙ q))
    (isoComp-cong (idIso α) (invIso (inverse-composite p′ p)) ∙ isoComp-assoc-at α (invIso p) (invIso p′)) ∙
  (invIso (isoComp-assoc-at q′ q ((α ∙ invIso p) ∙ invIso p′)) ∙
    isoComp-cong (idIso q′) (isoComp-assoc-at q (α ∙ invIso p) (invIso p′)))

module Restriction {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (mapPost {C = T} f) (mapPost g) X) where

  p = Cone.left s
  q = Cone.right s
  τ = Cone.match s
  F = mapPost {C = T} f
  G = mapPost {C = T} g
  R = productMap r (id T)
  af = comp-assoc r p F
  ag = comp-assoc r q G
  bf = mapUncurry-pre {C = T} {D = E} (F ∘ p) r
  bg = mapUncurry-pre {C = T} {D = E} (G ∘ q) r
  Ef = mapPost-uncurry {C = T} f (p ∘ r) ∙ mapUncurryIso {C = T} {D = E} af
  Eg = mapPost-uncurry {C = T} g (q ∘ r) ∙ mapUncurryIso {C = T} {D = E} ag
  Ef′ = comp-assoc R (mapUncurry p) f ∙ (mapPost-uncurry {C = T} f p ▷ R)
  Eg′ = comp-assoc R (mapUncurry q) g ∙ (mapPost-uncurry {C = T} g q ▷ R)
  ℓ = mapUncurry-pre p r
  ρ = mapUncurry-pre q r
  source : Cone f g (Y × T)
  source = uncurryCone {f = f} {g = g} (conePre r s)
  target : Cone f g (Y × T)
  target = conePre R (uncurryCone {f = f} {g = g} s)
  rawSource = changeEndpoints Ef Eg (mapUncurryIso {C = T} {D = E} (τ ▷ r))
  rawTarget = changeEndpoints Ef′ Eg′ (mapUncurryIso {C = T} {D = E} τ ▷ R)

  abstract
    source-normal : Iso₂ (Cone.match source) rawSource
    source-normal = endpoints-iterated (mapUncurryIso {C = T} {D = E} af) (mapUncurryIso {C = T} {D = E} ag)
        (mapPost-uncurry {C = T} f (p ∘ r)) (mapPost-uncurry {C = T} g (q ∘ r)) (mapUncurryIso {C = T} {D = E} (τ ▷ r)) ∙
      isoComp-cong (idIso (mapPost-uncurry {C = T} g (q ∘ r)))
        (isoComp-cong
          (isoComp-cong (idIso (mapUncurryIso {C = T} {D = E} ag))
            (isoComp-cong (idIso (mapUncurryIso {C = T} {D = E} (τ ▷ r))) (mapUncurryIso-inverse {C = T} {D = E} af) ∙
              mapUncurryIso-comp {C = T} {D = E} (τ ▷ r) (invIso af)) ∙
            mapUncurryIso-comp {C = T} {D = E} ag ((τ ▷ r) ∙ invIso af))
          (idIso (invIso (mapPost-uncurry {C = T} f (p ∘ r)))))
  
    target-normal : Iso₂ (Cone.match target) rawTarget
    target-normal = endpoints-iterated (mapPost-uncurry {C = T} f p ▷ R) (mapPost-uncurry {C = T} g q ▷ R)
        (comp-assoc R (mapUncurry p) f) (comp-assoc R (mapUncurry q) g) (mapUncurryIso {C = T} {D = E} τ ▷ R) ∙
      isoComp-cong (idIso (comp-assoc R (mapUncurry q) g))
        (isoComp-cong
          (isoComp-cong (idIso (mapPost-uncurry {C = T} g q ▷ R))
            (isoComp-cong (idIso (mapUncurryIso {C = T} {D = E} τ ▷ R)) (pre-inverse (mapPost-uncurry {C = T} f p) R) ∙
              preWhisker-isoComp-at (mapUncurryIso {C = T} {D = E} τ) (invIso (mapPost-uncurry {C = T} f p)) R) ∙
            preWhisker-isoComp-at (mapPost-uncurry {C = T} g q) (mapUncurryIso {C = T} {D = E} τ ∙ invIso (mapPost-uncurry {C = T} f p)) R)
          (idIso (invIso (comp-assoc R (mapUncurry p) f))))
  
```
