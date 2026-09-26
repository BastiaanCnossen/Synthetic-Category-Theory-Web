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

module SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingPre
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ hiding (funUncurryIso-comp; funUncurryIso-inverse; funUncurry-restrict-inputs)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingSubstitution 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingProofs 𝒯 M ℱ

open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingNormalization as Normalization

module Restriction {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (funPost {C = T} f) (funPost g) X) where

  open Normalization.Restriction 𝒯 M ℱ r s

  abstract
    rawSquare : (rawTarget ∙ (f ◁ ℓ)) =₂ ((g ◁ ρ) ∙ rawSource)
    rawSquare = paste-iso-squares
      (funUncurryIso (τ ▷ r) ∙ Ef ⁻¹) ((funUncurryIso τ ▷ R) ∙ Ef′ ⁻¹)
      Eg Eg′ (f ◁ ℓ) bg (g ◁ ρ)
      (paste-iso-squares (Ef ⁻¹) (Ef′ ⁻¹) (funUncurryIso (τ ▷ r)) (funUncurryIso τ ▷ R)
        (f ◁ ℓ) bf bg
        (move-square Ef′ bf (f ◁ ℓ) Ef ((funPost-uncurry-restrict f p r) ⁻¹ ∙
          isoComp-assoc-at (comp-assoc R (funUncurry p) f) (funPost-uncurry f p ▷ R) bf))
        ((funUncurry-restrict-inputs τ r) ⁻¹))
      ((funPost-uncurry-restrict g q r) ⁻¹ ∙
        isoComp-assoc-at (comp-assoc R (funUncurry q) g) (funPost-uncurry g q ▷ R) bg)
  
  comparison : ConeIso source target
  comparison = record { leftIso = ℓ ; rightIso = ρ
    ; compatible = isoComp-cong (idIso (g ◁ ρ)) (source-normal ⁻¹) ∙
      (rawSquare ∙ isoComp-cong target-normal (idIso (f ◁ ℓ))) }

uncurryCone-restrict : {X Y T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Y X) (s : Cone (funPost {C = T} f) (funPost g) X) →
  ConeIso (uncurryCone (conePre r s)) (conePre (productMap r (id T)) (uncurryCone s))
uncurryCone-restrict = Restriction.comparison
```


