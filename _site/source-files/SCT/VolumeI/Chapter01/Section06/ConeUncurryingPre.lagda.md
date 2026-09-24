# Uncurrying a restricted cone

Restriction of a cone commutes with uncurrying. The matching comparison
uses the postcomposition substitution law and the naturality of uncurrying
on isomorphisms, including the inverse and associativity comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.ConeUncurryingPre
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M hiding (mapUncurryIso-comp)
open import SCT.VolumeI.Chapter01.Section06.ConeUncurrying 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.MappingSubstitution 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.MappingProofs 𝒯 M

open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯 using (changeEndpoints)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

import SCT.VolumeI.Chapter01.Section06.ConeUncurryingNormalization as Normalization

module Restriction {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (mapPost {C = T} f) (mapPost g) X) where

  open Normalization.Restriction 𝒯 M r s

  abstract
    rawSquare : (rawTarget ∙ (f ◁ ℓ)) =₂ ((g ◁ ρ) ∙ rawSource)
    rawSquare = paste-iso-squares
      (mapUncurryIso (τ ▷ r) ∙ Ef ⁻¹) ((mapUncurryIso τ ▷ R) ∙ Ef′ ⁻¹)
      Eg Eg′ (f ◁ ℓ) bg (g ◁ ρ)
      (paste-iso-squares (Ef ⁻¹) (Ef′ ⁻¹) (mapUncurryIso (τ ▷ r)) (mapUncurryIso τ ▷ R)
        (f ◁ ℓ) bf bg
        (move-square Ef′ bf (f ◁ ℓ) Ef ((mapPost-uncurry-restrict f p r) ⁻¹ ∙
          isoComp-assoc-at (comp-assoc R (mapUncurry p) f) (mapPost-uncurry f p ▷ R) bf))
        ((mapUncurry-restrict-inputs τ r) ⁻¹))
      ((mapPost-uncurry-restrict g q r) ⁻¹ ∙
        isoComp-assoc-at (comp-assoc R (mapUncurry q) g) (mapPost-uncurry g q ▷ R) bg)
  
  comparison : ConeIso source target
  comparison = record { leftIso = ℓ ; rightIso = ρ
    ; compatible = isoComp-cong (idIso (g ◁ ρ)) (source-normal ⁻¹) ∙
      (rawSquare ∙ isoComp-cong target-normal (idIso (f ◁ ℓ))) }

uncurryCone-restrict : {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (mapPost {C = T} f) (mapPost g) X) →
  ConeIso (uncurryCone (conePre r s)) (conePre (productMap r (id T)) (uncurryCone s))
uncurryCone-restrict = Restriction.comparison
```
