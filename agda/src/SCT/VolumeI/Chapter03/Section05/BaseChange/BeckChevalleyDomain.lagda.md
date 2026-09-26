# The evaluation-domain cone in base change

The expanded cone defining Beck–Chevalley is the pasting of the source
pullback with the given square, followed by projection from the target
pullback. This identification changes only the association of the
specified matching paths.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyDomain
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)

module Domain {S T S′ T′ D : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (g : MAP D T) where
  h = Cone.left square
  p′ = Cone.right square
  E = Pullback g b
  t : MAP E T′
  t = pullback₂
  source = Pullback t p′
  j₁ : MAP source E
  j₁ = pullback₁
  j₂ : MAP source S′
  j₂ = pullback₂
  π : MAP E D
  π = pullback₁
  projected : FunctorOver (b ∘ t) g
  projected = record { lift = π ; comparison = pullbackMatch }
  module Paste = PasteCones t b (coneSwap square)

  cone : Cone g p source
  cone = record { left = π ∘ j₁ ; right = h ∘ j₂
    ; match = comp-assoc j₂ h p ∙
        ((Cone.match square ⁻¹ ▷ j₂) ∙
          ((comp-assoc j₂ p′ b) ⁻¹ ∙
            ((b ◁ pullbackMatch {f = t} {p′}) ∙
              (comp-assoc j₁ t b ∙
                ((pullbackMatch {f = g} {b} ▷ j₁) ∙ (comp-assoc j₁ π g) ⁻¹))))) }

  pasted = Action.value p projected (Paste.flatten (pullbackCone t p′))
  into : MAP source (Pullback g p)
  into = pullbackLift cone

  into-over : FunctorOver (h ∘ j₂) (pullback₂ {f = g} {p})
  into-over = record { lift = into ; comparison = pullbackLift-β₂ cone }

  private
    A = comp-assoc j₂ h p
    s = Cone.match square ⁻¹ ▷ j₂
    B = (comp-assoc j₂ p′ b) ⁻¹
    ρ = b ◁ pullbackMatch {f = t} {p′}
    J = comp-assoc j₁ t b
    tail = (pullbackMatch {f = g} {b} ▷ j₁) ∙ (comp-assoc j₁ π g) ⁻¹
    ν = A ∙ (s ∙ B)
    ζ = ρ ∙ J
    rest = ρ ∙ (J ∙ tail)

  abstract
    matching : Cone.match pasted =₂ Cone.match cone
    matching = isoComp-cong (idIso A) (isoComp-assoc-at s B rest) ∙
      (isoComp-assoc-at A (s ∙ B) rest ∙
        (isoComp-cong (idIso ν) (isoComp-assoc-at ρ J tail) ∙ isoComp-assoc-at ν ζ tail))

  normalization : ConeIso cone pasted
  normalization = cone-match-change _ _ _ _ (matching ⁻¹)
```
