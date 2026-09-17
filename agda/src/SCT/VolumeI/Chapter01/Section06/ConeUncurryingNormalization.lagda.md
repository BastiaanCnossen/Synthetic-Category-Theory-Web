# Uncurrying a restricted cone

Restriction of a cone commutes with uncurrying. The matching comparison
uses the postcomposition substitution law and the naturality of uncurrying
on isomorphisms, including the inverse and associativity comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.ConeUncurryingNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ hiding (funUncurryIso-comp; funUncurryIso-inverse; funUncurry-pre-inputs)
open import SCT.VolumeI.Chapter01.Section06.ConeUncurrying 𝒯 M ℱ

open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.MappingProofs 𝒯 M ℱ

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
  (r : MAP Y X) (s : Cone (funPost {C = T} f) (funPost g) X) where

  p = Cone.left s
  q = Cone.right s
  τ = Cone.match s
  F = funPost {C = T} f
  G = funPost {C = T} g
  R = productMap r (id T)
  af = comp-assoc r p F
  ag = comp-assoc r q G
  bf = funUncurry-pre {C = T} {D = E} (F ∘ p) r
  bg = funUncurry-pre {C = T} {D = E} (G ∘ q) r
  Ef = funPost-uncurry {C = T} f (p ∘ r) ∙ funUncurryIso {C = T} {D = E} af
  Eg = funPost-uncurry {C = T} g (q ∘ r) ∙ funUncurryIso {C = T} {D = E} ag
  Ef′ = comp-assoc R (funUncurry p) f ∙ (funPost-uncurry {C = T} f p ▷ R)
  Eg′ = comp-assoc R (funUncurry q) g ∙ (funPost-uncurry {C = T} g q ▷ R)
  ℓ = funUncurry-pre p r
  ρ = funUncurry-pre q r
  source : Cone f g (Y × T)
  source = uncurryCone {f = f} {g = g} (conePre r s)
  target : Cone f g (Y × T)
  target = conePre R (uncurryCone {f = f} {g = g} s)
  rawSource = changeEndpoints Ef Eg (funUncurryIso {C = T} {D = E} (τ ▷ r))
  rawTarget = changeEndpoints Ef′ Eg′ (funUncurryIso {C = T} {D = E} τ ▷ R)

  abstract
    source-normal : Iso₂ (Cone.match source) rawSource
    source-normal = endpoints-iterated (funUncurryIso {C = T} {D = E} af) (funUncurryIso {C = T} {D = E} ag)
        (funPost-uncurry {C = T} f (p ∘ r)) (funPost-uncurry {C = T} g (q ∘ r)) (funUncurryIso {C = T} {D = E} (τ ▷ r)) ∙
      isoComp-cong (idIso (funPost-uncurry {C = T} g (q ∘ r)))
        (isoComp-cong
          (isoComp-cong (idIso (funUncurryIso {C = T} {D = E} ag))
            (isoComp-cong (idIso (funUncurryIso {C = T} {D = E} (τ ▷ r))) (funUncurryIso-inverse {C = T} {D = E} af) ∙
              funUncurryIso-comp {C = T} {D = E} (τ ▷ r) (invIso af)) ∙
            funUncurryIso-comp {C = T} {D = E} ag ((τ ▷ r) ∙ invIso af))
          (idIso (invIso (funPost-uncurry {C = T} f (p ∘ r)))))
  
    target-normal : Iso₂ (Cone.match target) rawTarget
    target-normal = endpoints-iterated (funPost-uncurry {C = T} f p ▷ R) (funPost-uncurry {C = T} g q ▷ R)
        (comp-assoc R (funUncurry p) f) (comp-assoc R (funUncurry q) g) (funUncurryIso {C = T} {D = E} τ ▷ R) ∙
      isoComp-cong (idIso (comp-assoc R (funUncurry q) g))
        (isoComp-cong
          (isoComp-cong (idIso (funPost-uncurry {C = T} g q ▷ R))
            (isoComp-cong (idIso (funUncurryIso {C = T} {D = E} τ ▷ R)) (pre-inverse (funPost-uncurry {C = T} f p) R) ∙
              preWhisker-isoComp-at (funUncurryIso {C = T} {D = E} τ) (invIso (funPost-uncurry {C = T} f p)) R) ∙
            preWhisker-isoComp-at (funPost-uncurry {C = T} g q) (funUncurryIso {C = T} {D = E} τ ∙ invIso (funPost-uncurry {C = T} f p)) R)
          (idIso (invIso (comp-assoc R (funUncurry p) f))))
  
```


