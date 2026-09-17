# Normalizing an application route

This finite pasting calculation is independent of the mapping term being
applied. Its hypotheses are the already specified endpoint comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.MappingProofCalculus as MappingProof

module SCT.VolumeI.Chapter01.Section03.ApplicationRouteNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where
open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open MappingProof 𝒯 M

module Assembly {Γ C D : CAT}
  {k₀ k₁ k₂ k₃ : MAP Γ (Map C D)} {u v : MAP Γ C}
  (α : NatIso k₂ k₃) (β : NatIso k₁ k₂) (γ : NatIso k₀ k₁)
  (ξ : NatIso u v) (coordinate : NatIso k₀ k₃)
  {S T O : MAP Γ D}
  (after : NatIso T (applyTerm k₂ v)) (e : NatIso S T)
  (sourceAfter : NatIso S (applyTerm k₁ v))
  (tail : NatIso S (applyTerm k₀ u))
  (outer : NatIso (applyTerm k₃ v) O) where

  first = applyTerm-cong α (idIso v)
  second = applyTerm-cong β (idIso v)
  third = applyTerm-cong γ ξ

  abstract
    comparison : Iso₂ (α ∙ (β ∙ γ)) coordinate
      → Iso₂ (after ∙ e) (second ∙ sourceAfter)
      → Iso₂ sourceAfter (third ∙ tail)
      → Iso₂ ((outer ∙ (first ∙ after)) ∙ e)
        (outer ∙ (applyTerm-cong coordinate ξ ∙ tail))
    comparison coordinate-law natural restrict =
      let joinInner = isoComp-cong
              (apply-cong-Iso₂ (idIso (β ∙ γ)) (isoComp-unitˡ-at ξ)) (idIso tail) ∙
            combine-apply β (idIso v) γ ξ tail
          joinOuter = isoComp-cong
              (apply-cong-Iso₂ coordinate-law (isoComp-unitˡ-at ξ)) (idIso tail) ∙
            combine-apply α (idIso v) (β ∙ γ) ξ tail
          normalize = joinOuter ∙
            isoComp-cong (idIso first) (joinInner ∙ isoComp-cong (idIso second) restrict)
          expand = isoComp-cong (idIso outer)
              (isoComp-cong (idIso first) natural ∙ isoComp-assoc-at first after e) ∙
            isoComp-assoc-at outer (first ∙ after) e
      in isoComp-cong (idIso outer) normalize ∙ expand
```