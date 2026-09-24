# Pulling back an equivalence

For `cor:Equivalences_Closed_Under_Pullback`, an equivalence on the right
allows us to fill a compatible cone comparison from its left leg. The
specified image of the lifted isomorphism supplies the compatibility proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackLifting 𝒯 P

coneIso-from-left : {C D E T : CAT} {f : MAP C E} {g : MAP D E} → IsEquiv g →
  (s t : Cone f g T) → (Cone.left s) =₁ (Cone.left t) → ConeIso s t
coneIso-from-left {f = f} {g} eg s t α = record
  { leftIso = α
  ; rightIso = FunctorLift.lift chosen
  ; compatible = isoComp-cong ((FunctorLift.comparison chosen) ⁻¹) (idIso τ) ∙
      ((isoComp-assoc-at b (τ ⁻¹) τ) ⁻¹ ∙
      (isoComp-cong (idIso b) ((isoComp-inverseˡ-at τ) ⁻¹) ∙
        (isoComp-unitʳ-at b) ⁻¹)) }
  where
  τ = Cone.match s
  b = Cone.match t ∙ (f ◁ α)
  chosen = postWhisker-lift g eg (b ∙ τ ⁻¹)

module BaseChangeEquivalence {C D E : CAT} (f : MAP C E) (g : MAP D E)
  (eg : IsEquiv g) where

  lifted : FunctorLift g f
  lifted = equiv-lift eg f

  inverseCone : Cone f g C
  inverseCone = record
    { left = id C
    ; right = FunctorLift.lift lifted
    ; match = (FunctorLift.comparison lifted) ⁻¹ ∙ comp-unitʳ f }

  inverse : MAP C (Pullback f g)
  inverse = pullbackLift inverseCone

  inverse-image : (pullback₁ ∘ inverse) =₁ (id C)
  inverse-image = pullbackLift-β₁ inverseCone

  inverse-section : (inverse ∘ pullback₁) =₁ (id (Pullback f g))
  inverse-section = pullback-reflect _ _ (coneIso-from-left eg _ _
    ((comp-unitʳ pullback₁) ⁻¹ ∙
      (comp-unitˡ pullback₁ ∙ ((inverse-image ▷ pullback₁) ∙ (comp-assoc pullback₁ inverse pullback₁) ⁻¹))))

  projection-isEquiv : IsEquiv (pullback₁ {f = f} {g})
  projection-isEquiv = record
    { inverse = inverse
    ; sectionIso = inverse-section ⁻¹
    ; retractionIso = inverse-image ⁻¹ }

pullback-equivalence : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEquiv g → IsEquiv (pullback₁ {f = f} {g})
pullback-equivalence = BaseChangeEquivalence.projection-isEquiv

degenerate-pullback : {C D E T : CAT} {f : MAP C E} {g : MAP D E} →
  IsEquiv g → (s : Cone f g T) → IsEquiv (Cone.left s) → IsPullback s
degenerate-pullback {f = f} {g} eg s es = equiv-cancel-left (pullbackLift s) pullback₁
  (pullback-equivalence f g eg) (equiv-transport ((pullbackLift-β₁ s) ⁻¹) es)

degenerate-pullback-converse : {C D E T : CAT} {f : MAP C E} {g : MAP D E} →
  IsEquiv g → (s : Cone f g T) → IsPullback s → IsEquiv (Cone.left s)
degenerate-pullback-converse {f = f} {g} eg s es = equiv-transport (pullbackLift-β₁ s)
  (equiv-compose (pullbackLift s) pullback₁ es (pullback-equivalence f g eg))
```
