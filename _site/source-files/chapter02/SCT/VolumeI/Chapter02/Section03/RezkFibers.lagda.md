# Conditional Rezk comparison of identification animae

Given an equivalence of the actual identity-isomorphism functor, the
identification anima is equivalent to the fiber of the actual isomorphism
endpoint functor. The comparison changes the diagonal leg of the cospan
through that identity-isomorphism functor.

Its computation laws retain both stages: the whole diagonal cone beta
from representability, and the whole mapped universal cone beta restricted
to that factor. The latter includes its full chosen matching square.
The hypothesis is explicit; this owner introduces no Rezk assumption.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section03.RezkFibers where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terms using (Equal)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (id-isEquiv; equiv-compose)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-compose; cone-inverse; cone-identification-restrict-One; cone-restrict-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality using (module SwappedCone)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback₁; pullback₂; pullback-cone; pullback-factor; pullback-factor-β)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality
  using (CospanMap; pullback-map; pullback-map-β; module CospanEquivalence)
open import SCT.VolumeI.Chapter01.Section06.RepresentabilityDiagonal using (module Diagonal)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms
  using (Iso; isoEndpoints; identityIso; identityIso-endpoints)

module _ {Γ : Context} where
  IsoBetween : {C : CAT Γ} → MAP One C → MAP One C → CAT Γ
  IsoBetween {C} x y = Pullback (pair x y) (isoEndpoints C)

  module IdentificationFiber (C : CAT Γ) (R : IsEquiv (identityIso C))
    (x y : MAP One C) where
    private
      point : MAP One (C × C)
      point = pair x y
      diagonal : MAP C (C × C)
      diagonal = pair (id C) (id C)
      module D = Diagonal {Γ = Γ} x y using (diagonal-cone; diagonal-isPullback)

    diagonal-cone : Cone point diagonal (Equal x y)
    diagonal-cone = cone-swap D.diagonal-cone

    diagonal-isPullback : IsPullback diagonal-cone
    diagonal-isPullback = SwappedCone.isPullback D.diagonal-cone D.diagonal-isPullback

    diagonal-factor : MAP (Equal x y) (Pullback point diagonal)
    diagonal-factor = pullback-factor diagonal-cone

    diagonal-image : ConeIdentification₁
      (cone-restrict diagonal-factor (pullback-cone point diagonal)) diagonal-cone
    diagonal-image = pullback-factor-β diagonal-cone

    change : CospanMap point diagonal point (isoEndpoints C)
    change = record
      { left = id One; right = identityIso C; base = id (C × C)
      ; left-square = (comp-unitˡ point) ⁻¹ ∙ comp-unitʳ point
      ; right-square = (comp-unitˡ diagonal) ⁻¹ ∙ identityIso-endpoints C }

    private
      module Change = CospanEquivalence change (id-isEquiv One) R (id-isEquiv (C × C))
        using (pullback-map-isEquiv)

    identification-to-iso : MAP (Equal x y) (IsoBetween x y)
    identification-to-iso = pullback-map change ∘ diagonal-factor

    identification-to-iso-isEquiv : IsEquiv identification-to-iso
    identification-to-iso-isEquiv = equiv-compose diagonal-factor (pullback-map change)
      diagonal-isPullback Change.pullback-map-isEquiv

    transported-universal : Cone point (isoEndpoints C) (Pullback point diagonal)
    transported-universal = CospanMap.map-cone change (pullback-cone point diagonal)

    comparison-cone : Cone point (isoEndpoints C) (Equal x y)
    comparison-cone = cone-restrict diagonal-factor transported-universal

    comparison-image : ConeIdentification₁
      (cone-restrict identification-to-iso (pullback-cone point (isoEndpoints C))) comparison-cone
    comparison-image = cone-compose
      (cone-identification-restrict-One diagonal-factor (pullback-map-β change))
      (cone-inverse (cone-restrict-assoc diagonal-factor (pullback-map change)
        (pullback-cone point (isoEndpoints C))))

    point-image : (pullback₁ {f = point} {g = isoEndpoints C} ∘ identification-to-iso)
      =₁ Cone.left comparison-cone
    point-image = ConeIdentification₁.left comparison-image

    iso-image : (pullback₂ {f = point} {g = isoEndpoints C} ∘ identification-to-iso)
      =₁ Cone.right comparison-cone
    iso-image = ConeIdentification₁.right comparison-image
```
