# Restricting the terminal constant comparison

The comparison from a constant absolute point to that point restricts to
`const-pre`. The proof uses the triangle and naturality of the associator;
uniqueness is invoked only for maps and identifications into the terminal
category. Cancelling its inverse gives the endpoint normalization for
constant families of an absolute morphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section04.Substitution.ConstantPointRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
import SCT.VolumeI.Chapter01.Section03.Equivalences as TerminalComparisons
open TerminalComparisons.TerminalTargets vocabulary terminal products productLaws composition
  using (terminal-Iso₂)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as TerminalUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open TerminalUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

abstract
  const-One-restrict : {Γ C : CAT} (z : Obj-abs C) →
    (const-One z ▷ terminate Γ) =₂ const-pre z (terminate Γ)
  const-One-restrict {Γ} z =
    isoComp-cong (postWhisker z ◁ terminal-Iso₂ (ρ ∙ (δ ▷ t)) σ) (idIso α) ∙
    (isoComp-cong ((postWhisker-isoComp-at z ρ (δ ▷ t)) ⁻¹) (idIso α) ∙
    ((isoComp-assoc-at (z ◁ ρ) (z ◁ (δ ▷ t)) α) ⁻¹ ∙
    (isoComp-cong (idIso (z ◁ ρ)) (whisker-mixed-at δ t z) ∙
    (isoComp-assoc-at (z ◁ ρ) (comp-assoc t (id One) z) ((z ◁ δ) ▷ t) ∙
    (isoComp-cong (triangle-whiskered t z) (idIso ((z ◁ δ) ▷ t)) ∙
      preWhisker-isoComp-at (comp-unitʳ z) (z ◁ δ) t)))))
    where
    t : MAP Γ One
    t = terminate Γ
    δ : terminate One =₁ id One
    δ = terminal-iso (terminate One) (id One)
    ρ : (id One ∘ t) =₁ t
    ρ = comp-unitˡ t
    σ : (terminate One ∘ t) =₁ t
    σ = terminal-iso (terminate One ∘ t) t
    α : ((z ∘ terminate One) ∘ t) =₁ (z ∘ (terminate One ∘ t))
    α = comp-assoc t (terminate One) z

  const-One-cancel : {Γ C : CAT} (z : Obj-abs C) →
    (const-pre z (terminate Γ) ∙ ((const-One z) ⁻¹ ▷ terminate Γ)) =₂
      idIso (const {P = Γ} z)
  const-One-cancel {Γ} z = isoComp-inverseʳ-at (const-One z ▷ terminate Γ) ∙
    isoComp-cong ((const-One-restrict z) ⁻¹) (pre-inverse (const-One z) (terminate Γ))
```
