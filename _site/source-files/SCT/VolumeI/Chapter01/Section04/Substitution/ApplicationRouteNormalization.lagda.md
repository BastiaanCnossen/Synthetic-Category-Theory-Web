# Normalizing an application route

This finite pasting calculation is independent of the mapping term being
applied. Its hypotheses are the already specified endpoint comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.Calculus.Squares as Squares
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.Substitution.MappingProofCalculus as MappingProof

module SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRouteNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where
open Setup 𝒯
private
  module Paste (X Y : CAT) = Squares (comparisonAlgebra X Y) (comparisonLaws X Y)
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open MappingProof 𝒯 M

module Assembly {Γ C D : CAT}
  {k₀ k₁ k₂ k₃ : MAP Γ (Map C D)} {u v : MAP Γ C}
  (α : k₂ =₁ k₃) (β : k₁ =₁ k₂) (γ : k₀ =₁ k₁)
  (ξ : u =₁ v) (coordinate : k₀ =₁ k₃)
  {S T O : MAP Γ D}
  (after : T =₁ (applyTerm k₂ v)) (e : S =₁ T)
  (sourceAfter : S =₁ (applyTerm k₁ v))
  (tail : S =₁ (applyTerm k₀ u))
  (outer : (applyTerm k₃ v) =₁ O) where

  first = applyTerm-cong α (idIso v)
  second = applyTerm-cong β (idIso v)
  third = applyTerm-cong γ ξ

  abstract
    comparison : (α ∙ (β ∙ γ)) =₂ coordinate
      → (after ∙ e) =₂ (second ∙ sourceAfter)
      → sourceAfter =₂ (third ∙ tail)
      → ((outer ∙ (first ∙ after)) ∙ e) =₂
        (outer ∙ (applyTerm-cong coordinate ξ ∙ tail))
    comparison coordinate-law natural restrict =
      let joinInner = isoComp-cong
              (apply-cong-Iso₂ (idIso (β ∙ γ)) (isoComp-unitˡ-at ξ)) (idIso tail) ∙
            combine-apply β (idIso v) γ ξ tail
          joinOuter = isoComp-cong
              (apply-cong-Iso₂ coordinate-law (isoComp-unitˡ-at ξ)) (idIso tail) ∙
            combine-apply α (idIso v) (β ∙ γ) ξ tail
      in Paste.normalize-comparison-route Γ D
        outer first second third after e sourceAfter tail
        (applyTerm-cong (β ∙ γ) ξ) (applyTerm-cong coordinate ξ)
        joinInner joinOuter natural restrict
```