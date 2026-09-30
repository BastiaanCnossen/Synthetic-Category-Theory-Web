# Transport through product separation

The quotient of the chosen separation frames survives a common change
of output coordinates. Cancellation supplies the literal normalized
parameter-change comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.SeparationFrameTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ChangedSeparationFrames as Changed
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {X Y A B : CAT} (h : MAP X Y) (f : MAP A B)
  {vY : MAP (Y × A) B} {vX : MAP (X × A) B}
  (θY : (f ∘ pr₂) =₁ vY) (θX : (f ∘ pr₂) =₁ vX)
  (t : (vY ∘ productMap h (id A)) =₁ vX) where
  module F = Changed.At 𝒯 M h f θY θX t
  open F using (σ; HB; δY; δX; κ; source-frame; target-frame)
  module S = F.S
  ν = (HB ◁ δX) ∙ (S.comparison ∙ (δY ⁻¹ ▷ σ))

  abstract
    cancel-separation : (S.target ∙ S.comparison) =₂ S.source
    cancel-separation = cancel-inverse S.target S.source ∙
      isoComp-cong (idIso S.target) S.normalization

    middle : (t ∙ (θY ▷ σ)) =₂ (θX ∙ F.N.source-second) →
      ((target-frame ∙ (HB ◁ δX)) ∙ S.comparison) =₂ (source-frame ∙ (δY ▷ σ))
    middle square = F.source-value square ∙
      isoComp-cong (idIso κ) cancel-separation ∙
      isoComp-assoc-at κ S.target S.comparison ∙
      isoComp-cong (F.target-value ⁻¹) (idIso S.comparison)

    value : (t ∙ (θY ▷ σ)) =₂ (θX ∙ F.N.source-second) →
      (target-frame ∙ ν) =₂ source-frame
    value square = cancel-right (δY ▷ σ) source-frame ∙
      isoComp-cong (middle square) (pre-inverse δY σ) ∙
      (isoComp-assoc-at (target-frame ∙ (HB ◁ δX)) S.comparison (δY ⁻¹ ▷ σ)) ⁻¹ ∙
      (isoComp-assoc-at target-frame (HB ◁ δX) (S.comparison ∙ (δY ⁻¹ ▷ σ))) ⁻¹
```
