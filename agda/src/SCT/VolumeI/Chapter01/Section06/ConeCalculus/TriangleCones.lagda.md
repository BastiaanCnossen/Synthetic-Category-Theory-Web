# Cones from a commuting triangle

A specified triangle determines a cone whose right leg is the identity.
Restricting it along a parameter map gives the normalized triangle cone.
The comparison retains the triangle identification and the right unitor;
its right leg is the left unitor of the parameter map.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as Coherence

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.TriangleCones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open Coherence vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)

module At {C E Γ : CAT} (b : MAP C E) (a : MAP Γ C) (e : MAP Γ E)
  (δ : (b ∘ a) =₁ e) where
  cone : Cone b e Γ
  cone = record { left = a ; right = id Γ ; match = (comp-unitʳ e) ⁻¹ ∙ δ }

  normalized : {X : CAT} (r : MAP X Γ) → Cone b e X
  normalized r = record { left = a ∘ r ; right = r
    ; match = (δ ▷ r) ∙ (comp-assoc r a b) ⁻¹ }

  restriction : {X : CAT} (r : MAP X Γ) → ConeIso (conePre r cone) (normalized r)
  restriction r = record
    { leftIso = idIso (a ∘ r) ; rightIso = comp-unitˡ r
    ; compatible = calculation ⁻¹ ∙
        (isoComp-unitʳ-at (Cone.match (normalized r)) ∙
          isoComp-cong (idIso (Cone.match (normalized r))) (postWhisker-idIso b (a ∘ r))) }
    where
    A = comp-assoc r a b
    U = comp-assoc r (id Γ) e
    L = e ◁ comp-unitˡ r
    ρ = comp-unitʳ e
    d = δ ▷ r
    inverse-law : ((ρ ▷ r) ∙ (ρ ⁻¹ ▷ r)) =₂ idIso (e ∘ r)
    inverse-law = preWhisker-idIso e r ∙
      ((preWhisker r ◁ isoComp-inverseʳ-at ρ) ∙
        (preWhisker-isoComp-at ρ (ρ ⁻¹) r) ⁻¹)
    calculation : (L ∙ Cone.match (conePre r cone)) =₂ Cone.match (normalized r)
    calculation = isoComp-unitˡ-at (d ∙ A ⁻¹) ∙
      (isoComp-cong inverse-law (idIso (d ∙ A ⁻¹)) ∙
      ((isoComp-assoc-at (ρ ▷ r) (ρ ⁻¹ ▷ r) (d ∙ A ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso (ρ ▷ r))
        (isoComp-assoc-at (ρ ⁻¹ ▷ r) d (A ⁻¹) ∙
          isoComp-cong (preWhisker-isoComp-at (ρ ⁻¹) δ r) (idIso (A ⁻¹))) ∙
      (isoComp-cong ((triangle-whiskered r e) ⁻¹)
        (idIso ((Cone.match cone ▷ r) ∙ A ⁻¹)) ∙
        (isoComp-assoc-at L U ((Cone.match cone ▷ r) ∙ A ⁻¹)) ⁻¹))))
```
