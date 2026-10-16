# Pullbacks under an arrow identification

The specified cospan-arrow identification induces the chosen forward and
backward maps. Their cone laws preserve and reflect pullback squares.
Left-arrow change uses the symmetry-based matching from ConeTransport; its
normalization to the conventional matching is explicit there.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PullbackArrowChange where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares

module _ {Γ : Context} where
  module ChangeLeftArrow {C D E : CAT Γ} {f f′ : MAP C E} (α : f =₁ f′) (g : MAP D E) where

    source : Cone f g (Pullback f g)
    source = pullback-cone f g
    target : Cone f′ g (Pullback f′ g)
    target = pullback-cone f′ g
    forward : MAP (Pullback f g) (Pullback f′ g)
    forward = pullback-factor (cone-change-left α source)
    backward : MAP (Pullback f′ g) (Pullback f g)
    backward = pullback-factor (cone-change-left (α ⁻¹) target)

    backward-forward : (backward ∘ forward) =₁ (id (Pullback f g))
    backward-forward = pullback-reflect _ _
      (cone-compose (cone-inverse (cone-restrict-id source))
      (cone-compose (cone-change-left-inverse α source)
      (cone-compose (cone-change-left-identification (α ⁻¹) (pullback-factor-β (cone-change-left α source)))
      (cone-compose (cone-change-left-restrict (α ⁻¹) forward target)
      (cone-compose (cone-identification-restrict-One forward (pullback-factor-β (cone-change-left (α ⁻¹) target)))
        (cone-inverse (cone-restrict-assoc forward backward source)))))))

    forward-backward : (forward ∘ backward) =₁ (id (Pullback f′ g))
    forward-backward = pullback-reflect _ _
      (cone-compose (cone-inverse (cone-restrict-id target))
      (cone-compose (cone-change-left-inverseʳ α target)
      (cone-compose (cone-change-left-identification α (pullback-factor-β (cone-change-left (α ⁻¹) target)))
      (cone-compose (cone-change-left-restrict α backward source)
      (cone-compose (cone-identification-restrict-One backward (pullback-factor-β (cone-change-left α source)))
        (cone-inverse (cone-restrict-assoc backward forward target)))))))

    forward-isEquiv : IsEquiv forward
    forward-isEquiv = record
      { inverse = backward ; left-inverse-law = backward-forward ⁻¹ ; right-inverse-law = forward-backward ⁻¹ }

    factor-law : {T : CAT Γ} (s : Cone f g T) →
      (pullback-factor (cone-change-left α s)) =₁ (forward ∘ pullback-factor s)
    factor-law s = pullback-reflect _ _
      (cone-compose (cone-inverse changed-factor-law) (pullback-factor-β (cone-change-left α s)))
      where
      changed-factor-law : ConeIdentification₁
        (cone-restrict (forward ∘ pullback-factor s) target) (cone-change-left α s)
      changed-factor-law = cone-compose (cone-change-left-identification α (pullback-factor-β s))
        (cone-compose (cone-change-left-restrict α (pullback-factor s) source)
        (cone-compose (cone-identification-restrict-One (pullback-factor s) (pullback-factor-β (cone-change-left α source)))
          (cone-inverse (cone-restrict-assoc (pullback-factor s) forward target))))

    preserve-pullback : {T : CAT Γ} (s : Cone f g T) → IsPullback s → IsPullback (cone-change-left α s)
    preserve-pullback s es = equiv-transport ((factor-law s) ⁻¹)
      (equiv-compose (pullback-factor s) forward es forward-isEquiv)

    reflect-pullback : {T : CAT Γ} (s : Cone f g T) → IsPullback (cone-change-left α s) → IsPullback s
    reflect-pullback s es = equiv-cancel-left (pullback-factor s) forward forward-isEquiv
      (equiv-transport (factor-law s) es)
```
