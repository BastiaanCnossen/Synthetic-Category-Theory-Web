# Recovering cocones across the left pushout

If the left square is a pushout, every outer cocone comes from a right
cocone, and every comparison between flattened cocones lifts. The second
statement uses the prescribed left boundary of the pushout comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section08.PushoutExtensions as Extensions
import SCT.VolumeI.Chapter01.Section08.PushoutComparison as Comparison

module SCT.VolumeI.Chapter01.Section08.UniversalCoconePasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.CoconePasting 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost)

module UniversalPasting {A₁ A₂ A₃ B₁ B₂ : CAT}
  (g₁ : MAP A₁ A₂) (g₂ : MAP A₂ A₃)
  {h₁ : MAP B₁ B₂} {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂}
  (left : Square g₁ f₁ f₂ h₁) (universal : IsPushout left) (E : CAT) where

  module Paste = PasteCocones g₁ g₂ left
  module Left = Extensions.Extensions 𝒯 M P left universal E

  module LiftOuter (t : Cocone (g₂ ∘ g₁) f₁ E) where
    module Extension = Left.Lift (compositeCocone g₁ g₂ t)
    p : MAP A₃ E
    p = Cocone.left t
    q : MAP B₂ E
    q = Extension.value
    α : NatIso (q ∘ f₂) (p ∘ g₂)
    α = CoconeIso.leftIso Extension.comparison
    β : NatIso (q ∘ h₁) (Cocone.right t)
    β = CoconeIso.rightIso Extension.comparison

    value : Cocone g₂ f₂ E
    value = record { left = p ; right = q ; match = invIso α }

    restricted : CoconeIso (compositeCocone g₁ g₂ (Paste.flatten value)) (compositeCocone g₁ g₂ t)
    restricted = coconeIso-compose Extension.comparison (Paste.flatten-composite value)

    abstract
      comparison : CoconeIso (Paste.flatten value) t
      comparison = compositeCocone-compatible g₁ g₂ (Paste.flatten value) t (idIso p) β
        (CoconeIso.compatible
          (coconeIso-adjust restricted (idIso p ▷ g₂) β
            (invIso (preWhisker-idIso p g₂) ∙ isoComp-inverseʳ-at α)
            (isoComp-unitʳ-at β)))

  module ReflectFlattened {s t : Cocone g₂ f₂ E} (Ψ : CoconeIso (Paste.flatten s) (Paste.flatten t)) where
    left-comparison : CoconeIso (coconePost (Cocone.right s) Paste.ordinary)
      (coconePost (Cocone.right t) Paste.ordinary)
    left-comparison = coconeIso-compose (Paste.flatten-composite t)
      (coconeIso-compose (compositeCoconeIso g₁ g₂ Ψ)
        (coconeIso-inverse (Paste.flatten-composite s)))
    module Controlled = Comparison.PrescribedComparison 𝒯 M P left universal
      (Cocone.right s) (Cocone.right t) left-comparison
    α : NatIso (Cocone.left s) (Cocone.left t)
    α = CoconeIso.leftIso Ψ
    δ : NatIso (Cocone.right s) (Cocone.right t)
    δ = Controlled.lift
    τs : NatIso (Cocone.left s ∘ g₂) (Cocone.right s ∘ f₂)
    τs = Cocone.match s
    τt : NatIso (Cocone.left t ∘ g₂) (Cocone.right t ∘ f₂)
    τt = Cocone.match t

    abstract
      cancel-matching : Iso₂ ((τt ∙ ((α ▷ g₂) ∙ invIso τs)) ∙ τs) (τt ∙ (α ▷ g₂))
      cancel-matching = isoComp-cong (idIso τt)
        (isoComp-unitʳ-at (α ▷ g₂) ∙
        (isoComp-cong (idIso (α ▷ g₂)) (isoComp-inverseˡ-at τs) ∙
          isoComp-assoc-at (α ▷ g₂) (invIso τs) τs)) ∙
        isoComp-assoc-at τt ((α ▷ g₂) ∙ invIso τs) τs

    comparison : CoconeIso s t
    comparison = record
      { leftIso = α ; rightIso = δ
      ; compatible = isoComp-cong (invIso Controlled.left-image) (idIso τs) ∙ invIso cancel-matching }
```
