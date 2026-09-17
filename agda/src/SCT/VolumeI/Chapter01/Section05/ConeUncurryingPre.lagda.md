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

module SCT.VolumeI.Chapter01.Section05.ConeUncurryingPre
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M hiding (mapUncurryIso-comp)
open import SCT.VolumeI.Chapter01.Section05.ConeUncurrying 𝒯 M
open import SCT.VolumeI.Chapter01.Section05.MappingSubstitution 𝒯 M
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section05.MappingProofs 𝒯 M

open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯 using (changeEndpoints)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

import SCT.VolumeI.Chapter01.Section05.ConeUncurryingNormalization as Normalization

module Restriction {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (mapPost {C = T} f) (mapPost g) X) where

  open Normalization.Restriction 𝒯 M r s

  abstract
    rawSquare : Iso₂ (rawTarget ∙ (f ◁ ℓ)) ((g ◁ ρ) ∙ rawSource)
    rawSquare = paste-iso-squares
      (mapUncurryIso (τ ▷ r) ∙ invIso Ef) ((mapUncurryIso τ ▷ R) ∙ invIso Ef′)
      Eg Eg′ (f ◁ ℓ) bg (g ◁ ρ)
      (paste-iso-squares (invIso Ef) (invIso Ef′) (mapUncurryIso (τ ▷ r)) (mapUncurryIso τ ▷ R)
        (f ◁ ℓ) bf bg
        (move-square Ef′ bf (f ◁ ℓ) Ef (invIso (mapPost-uncurry-pre f p r) ∙
          isoComp-assoc-at (comp-assoc R (mapUncurry p) f) (mapPost-uncurry f p ▷ R) bf))
        (invIso (mapUncurry-pre-inputs τ r)))
      (invIso (mapPost-uncurry-pre g q r) ∙
        isoComp-assoc-at (comp-assoc R (mapUncurry q) g) (mapPost-uncurry g q ▷ R) bg)
  
  comparison : ConeIso source target
  comparison = record { leftIso = ℓ ; rightIso = ρ
    ; compatible = isoComp-cong (idIso (g ◁ ρ)) (invIso source-normal) ∙
      (rawSquare ∙ isoComp-cong target-normal (idIso (f ◁ ℓ))) }

uncurryCone-pre : {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (mapPost {C = T} f) (mapPost g) X) →
  ConeIso (uncurryCone (conePre r s)) (conePre (productMap r (id T)) (uncurryCone s))
uncurryCone-pre = Restriction.comparison
```
