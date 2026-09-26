# Lifting a prescribed identification after restriction

If restriction embeds the mapping anima, an identification between two
restricted functors lifts together with its prescribed image. This is
stronger than constructing some identification of the original functors.

Name the functors, encode the given identification using decoding, and
lift it through the embedding. Naturality of decoding then recovers the
original specified identification after restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.RestrictionLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingCalculus 𝒯 M using (decodePre; decodePre-absolute)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodedLegCalculus 𝒯 using (decoded-leg)
open import SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting 𝒯 P using (embedding-lift)

module Lift {B C D : CAT} (r : MAP B C) (er : IsEmbedding (mapPre {D = D} r))
  (f g : MAP C D) (α : (f ∘ r) =₁ (g ∘ r)) where

  f′ = nameMap f
  g′ = nameMap g
  restricted-f = mapPre r ∘ f′
  restricted-g = mapPre r ∘ g′

  desired : decodeMap restricted-f =₁ decodeMap restricted-g
  desired = (decodePre r g′) ⁻¹ ∙
    ((decode-name g ▷ r) ⁻¹ ∙ (α ∙ ((decode-name f ▷ r) ∙ decodePre r f′)))

  encoded : restricted-f =₁ restricted-g
  encoded = decodeMap-reflect restricted-f restricted-g desired

  chosen : FunctorLift (postWhisker (mapPre r)) encoded
  chosen = embedding-lift (mapPre r) er f′ g′ encoded

  decoded : decodeMap f′ =₁ decodeMap g′
  decoded = decodeMapIso (FunctorLift.lift chosen)

  lift : f =₁ g
  lift = decode-name g ∙ (decoded ∙ (decode-name f) ⁻¹)

  abstract
    image : (lift ▷ r) =₂ α
    image = decoded-leg (decodePre r f′) (decodePre r g′)
      (decode-name f ▷ r) (decode-name g ▷ r) α
      (decodeMapIso (mapPre r ◁ FunctorLift.lift chosen)) (decoded ▷ r)
      (decodePre-absolute r (FunctorLift.lift chosen))
      (decodeMap-reflect-β restricted-f restricted-g desired ∙
        (decodeMap-isoMap restricted-f restricted-g ◁ FunctorLift.comparison chosen)) ∙ normal
      where
      normal : (lift ▷ r) =₂
        changeEndpoints (decode-name f ▷ r) (decode-name g ▷ r) (decoded ▷ r)
      normal = isoComp-cong (idIso (decode-name g ▷ r))
        (isoComp-cong (idIso (decoded ▷ r)) (pre-inverse (decode-name f) r) ∙
          preWhisker-isoComp-at decoded ((decode-name f) ⁻¹) r) ∙
        preWhisker-isoComp-at (decode-name g) (decoded ∙ (decode-name f) ⁻¹) r

  factorization : FunctorLift (preWhisker r) α
  factorization = record { lift = lift ; comparison = image }
```
