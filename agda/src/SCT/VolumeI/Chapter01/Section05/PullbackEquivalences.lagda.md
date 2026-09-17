# Pulling back an equivalence

For `cor:Equivalences_Closed_Under_Pullback`, an equivalence on the right
allows us to fill a compatible cone comparison from its left leg. The
specified image of the lifted isomorphism supplies the compatibility proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P

coneIso-from-left : {C D E T : CAT} {f : MAP C E} {g : MAP D E} → IsEquiv g →
  (s t : Cone f g T) → NatIso (Cone.left s) (Cone.left t) → ConeIso s t
coneIso-from-left {f = f} {g} eg s t α = record
  { leftIso = α
  ; rightIso = FunctorLift.lift chosen
  ; compatible = isoComp-cong (invIso (FunctorLift.comparison chosen)) (idIso τ) ∙
      (invIso (isoComp-assoc-at b (invIso τ) τ) ∙
      (isoComp-cong (idIso b) (invIso (isoComp-inverseˡ-at τ)) ∙
        invIso (isoComp-unitʳ-at b))) }
  where
  τ = Cone.match s
  b = Cone.match t ∙ (f ◁ α)
  chosen = postWhisker-lift g eg (b ∙ invIso τ)

module BaseChangeEquivalence {C D E : CAT} (f : MAP C E) (g : MAP D E)
  (eg : IsEquiv g) where

  lifted : FunctorLift g f
  lifted = equiv-lift eg f

  inverseCone : Cone f g C
  inverseCone = record
    { left = id C
    ; right = FunctorLift.lift lifted
    ; match = invIso (FunctorLift.comparison lifted) ∙ comp-unitʳ f }

  inverse : MAP C (Pullback f g)
  inverse = pbLift inverseCone

  inverse-image : NatIso (pb₁ ∘ inverse) (id C)
  inverse-image = pbLift-β₁ inverseCone

  inverse-section : NatIso (inverse ∘ pb₁) (id (Pullback f g))
  inverse-section = pullback-reflect _ _ (coneIso-from-left eg _ _
    (invIso (comp-unitʳ pb₁) ∙
      (comp-unitˡ pb₁ ∙ ((inverse-image ▷ pb₁) ∙ invIso (comp-assoc pb₁ inverse pb₁)))))

  projection-isEquiv : IsEquiv (pb₁ {f = f} {g})
  projection-isEquiv = record
    { inverse = inverse
    ; sectionIso = invIso inverse-section
    ; retractionIso = invIso inverse-image }

pullback-equivalence : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEquiv g → IsEquiv (pb₁ {f = f} {g})
pullback-equivalence = BaseChangeEquivalence.projection-isEquiv

degenerate-pullback : {C D E T : CAT} {f : MAP C E} {g : MAP D E} →
  IsEquiv g → (s : Cone f g T) → IsEquiv (Cone.left s) → IsPullback s
degenerate-pullback {f = f} {g} eg s es = equiv-cancel-left (pbLift s) pb₁
  (pullback-equivalence f g eg) (equiv-transport (invIso (pbLift-β₁ s)) es)

degenerate-pullback-converse : {C D E T : CAT} {f : MAP C E} {g : MAP D E} →
  IsEquiv g → (s : Cone f g T) → IsPullback s → IsEquiv (Cone.left s)
degenerate-pullback-converse {f = f} {g} eg s es = equiv-transport (pbLift-β₁ s)
  (equiv-compose (pbLift s) pb₁ es (pullback-equivalence f g eg))
```
