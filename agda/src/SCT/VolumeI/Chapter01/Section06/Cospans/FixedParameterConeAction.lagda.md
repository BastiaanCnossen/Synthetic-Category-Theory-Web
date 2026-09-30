# Mapping cones while keeping the parameter fixed

For a map of cospans whose parameter map is the identity, the mapped
cone may retain the original parameter leg. The comparison removes the
identity functor and its unitors while preserving the specified matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.FixedParameterConeAction
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (triangle-whiskered)

module Along {C D Z E Γ : CAT} (u : MAP C D) (a₀ : MAP Γ D)
  (f : MAP C E) (w : MAP E Z) (b : MAP D Z) (a₁ : MAP Γ Z)
  (α : (w ∘ f) =₁ (b ∘ u)) (δ : (b ∘ a₀) =₁ a₁) where

  cospan : CospanMap u a₀ w a₁
  cospan = record { left = f ; right = id Γ ; base = b
    ; leftSquare = α ; rightSquare = δ ⁻¹ ∙ comp-unitʳ a₁ }

  left-route : {X : CAT} (p : MAP X C) → (w ∘ (f ∘ p)) =₁ (b ∘ (u ∘ p))
  left-route p = comp-assoc p u b ∙ ((α ▷ p) ∙ (comp-assoc p f w) ⁻¹)

  value : {X : CAT} → Cone u a₀ X → Cone w a₁ X
  value s = record { left = f ∘ Cone.left s ; right = Cone.right s
    ; match = (δ ▷ Cone.right s) ∙ ((comp-assoc (Cone.right s) a₀ b) ⁻¹ ∙
        ((b ◁ Cone.match s) ∙ left-route (Cone.left s))) }

  module At {X : CAT} (s : Cone u a₀ X) where
    private
      p = Cone.left s
      r = Cone.right s
      R = comp-unitʳ a₁
      A = comp-assoc r (id Γ) a₁
      B = ((δ ⁻¹ ∙ R) ⁻¹) ▷ r
      C₀ = (comp-assoc r a₀ b) ⁻¹
      tail = (b ◁ Cone.match s) ∙ left-route p
      unit = a₁ ◁ comp-unitˡ r

      abstract
        inverse-normal : ((δ ⁻¹ ∙ R) ⁻¹) =₂ (R ⁻¹ ∙ δ)
        inverse-normal = isoComp-cong (idIso (R ⁻¹)) (inverse-inverse δ) ∙ inverse-composite (δ ⁻¹) R

        restricted-inverse : B =₂ ((R ▷ r) ⁻¹ ∙ (δ ▷ r))
        restricted-inverse = isoComp-cong (pre-inverse R r) (idIso (δ ▷ r)) ∙
          (preWhisker-isoComp-at (R ⁻¹) δ r ∙ (preWhisker r ◁ inverse-normal))

        right-route : ((unit ∙ A) ∙ B) =₂ (δ ▷ r)
        right-route = cancel-inverse (R ▷ r) (δ ▷ r) ∙
          isoComp-cong ((triangle-whiskered r a₁) ⁻¹) restricted-inverse

        matching : (unit ∙ Cone.match (CospanMap.mapCone cospan s)) =₂ Cone.match (value s)
        matching = isoComp-cong right-route (idIso (C₀ ∙ tail)) ∙
          ((isoComp-assoc-at (unit ∙ A) B (C₀ ∙ tail)) ⁻¹ ∙
            (isoComp-assoc-at unit A (B ∙ (C₀ ∙ tail))) ⁻¹)

    comparison : ConeIso (CospanMap.mapCone cospan s) (value s)
    comparison = record { leftIso = idIso (f ∘ p) ; rightIso = comp-unitˡ r
      ; compatible = matching ⁻¹ ∙
          (isoComp-unitʳ-at (Cone.match (value s)) ∙
            isoComp-cong (idIso (Cone.match (value s))) (postWhisker-idIso w (f ∘ p))) }
```
