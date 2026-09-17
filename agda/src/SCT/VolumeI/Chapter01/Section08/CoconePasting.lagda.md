# Flattening cocones

A cocone on the right span pastes with the fixed left square to give a
cocone on the outer span. Restricting it to the left span recovers
postcomposition of the left square, with the original matching as its
left comparison. This makes the effect on comparisons explicit.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)

module SCT.VolumeI.Chapter01.Section08.CoconePasting
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.CompositeCocones 𝒯 public
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost; cocone-action)

module PasteCocones {A₁ A₂ A₃ B₁ B₂ : CAT}
  (g₁ : MAP A₁ A₂) (g₂ : MAP A₂ A₃)
  {h₁ : MAP B₁ B₂} {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂}
  (left : Square g₁ f₁ f₂ h₁) where

  ordinary : Cocone g₁ f₁ B₂
  ordinary = squareCocone left

  flatten : {E : CAT} → Cocone g₂ f₂ E → Cocone (g₂ ∘ g₁) f₁ E
  flatten s = record
    { left = Cocone.left s ; right = Cocone.right s ∘ h₁
    ; match = Cocone.match (coconePost (Cocone.right s) ordinary) ∙
        ((Cocone.match s ▷ g₁) ∙ invIso (comp-assoc g₁ g₂ (Cocone.left s))) }

  flatten-match : {E : CAT} (s : Cocone g₂ f₂ E) →
    =₂ (Cocone.match (compositeCocone g₁ g₂ (flatten s)))
      (Cocone.match (coconePost (Cocone.right s) ordinary) ∙ (Cocone.match s ▷ g₁))
  flatten-match s = isoComp-cong (idIso ν)
    (isoComp-unitʳ-at ρ ∙
    (isoComp-cong (idIso ρ) (isoComp-inverseˡ-at A) ∙ isoComp-assoc-at ρ (invIso A) A)) ∙
    isoComp-assoc-at ν (ρ ∙ invIso A) A
    where
    ν = Cocone.match (coconePost (Cocone.right s) ordinary)
    ρ = Cocone.match s ▷ g₁
    A = comp-assoc g₁ g₂ (Cocone.left s)

  flatten-composite : {E : CAT} (s : Cocone g₂ f₂ E) →
    CoconeIso (compositeCocone g₁ g₂ (flatten s)) (coconePost (Cocone.right s) ordinary)
  flatten-composite s = record
    { leftIso = Cocone.match s ; rightIso = idIso (Cocone.right s ∘ h₁)
    ; compatible = isoComp-cong (invIso (preWhisker-idIso (Cocone.right s ∘ h₁) f₁)) (idIso σ) ∙
        (invIso (isoComp-unitˡ-at σ) ∙ invIso (flatten-match s)) }
    where
    σ = Cocone.match (compositeCocone g₁ g₂ (flatten s))

  flatten-iso : {E : CAT} {s t : Cocone g₂ f₂ E} →
    CoconeIso s t → CoconeIso (flatten s) (flatten t)
  flatten-iso {s = s} {t} Φ = compositeCocone-compatible g₁ g₂ (flatten s) (flatten t) α (β ▷ h₁)
    (isoComp-cong (idIso ((β ▷ h₁) ▷ f₁)) (invIso (flatten-match s)) ∙
    (paste-squares ρs ρt νs νt ((α ▷ g₂) ▷ g₁) ((β ▷ f₂) ▷ g₁) ((β ▷ h₁) ▷ f₁)
      restricted (CoconeIso.compatible (cocone-action ordinary β)) ∙
      isoComp-cong (flatten-match t) (idIso ((α ▷ g₂) ▷ g₁))))
    where
    α = CoconeIso.leftIso Φ
    β = CoconeIso.rightIso Φ
    ρs = Cocone.match s ▷ g₁
    ρt = Cocone.match t ▷ g₁
    νs = Cocone.match (coconePost (Cocone.right s) ordinary)
    νt = Cocone.match (coconePost (Cocone.right t) ordinary)
    restricted : =₂ (ρt ∙ ((α ▷ g₂) ▷ g₁)) (((β ▷ f₂) ▷ g₁) ∙ ρs)
    restricted = preWhisker-isoComp-at (β ▷ f₂) (Cocone.match s) g₁ ∙
      ((preWhisker g₁ ◁ CoconeIso.compatible Φ) ∙
        invIso (preWhisker-isoComp-at (Cocone.match t) (α ▷ g₂) g₁))
```
