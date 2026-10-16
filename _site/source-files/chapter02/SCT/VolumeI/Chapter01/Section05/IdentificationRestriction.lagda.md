# Identifications from coproduct restrictions

Restricting an identification to the two summands is an equivalence on the
full identification anima. First prove this for decoded names, using the
decoding–precomposition squares. Endpoint change along decode-name then
gives the result for arbitrary external functors. Factoring prescribed
restriction families through this equivalence retains their whole image
equation, and projecting it gives both summand equations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section05.IdentificationRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus using (pair-pre; project-pair₁; project-pair₂)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-cancel-right; equiv-transport)
open import SCT.VolumeI.Chapter01.Section03.Factorizations
  using (Factorization; factor; triangle; factor-through-equiv)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints₌; changeEndpoints₌-isEquiv; preWhisker-changeEndpoints-square)
open import SCT.VolumeI.Chapter01.Section03.Products.Equivalences
  using (pair-post-isEquiv; pair-squares-isEquiv; paired-postWhisker-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Points
  using (name; decode; decode-name; decode⁼-functor; decode⁼-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre)
open import SCT.VolumeI.Chapter01.Section04.Precomposition using (decode-pre; decode-pre-square)
open import SCT.VolumeI.Chapter01.Section05.Coproducts

module _ {Γ : Context} where
  coproductRestriction₌ : {C D E : CAT Γ} (h k : MAP (C ⊔ D) E)
    → MAP (Equal h k) (Equal (h ∘ in₁) (k ∘ in₁) × Equal (h ∘ in₂) (k ∘ in₂))
  coproductRestriction₌ h k = pair (preWhisker in₁) (preWhisker in₂)

  private
    module _ {C D E : CAT Γ} where
      open Terms.InContext (One {Γ}) using (Term)

      decoded-restriction-isEquiv : (x y : Term (Map (C ⊔ D) E))
        → IsEquiv (coproductRestriction₌ (decode x) (decode y))
      decoded-restriction-isEquiv x y =
        equiv-cancel-right (decode⁼-functor x y) (coproductRestriction₌ (decode x) (decode y))
          (decode⁼-isEquiv x y)
          (equiv-transport ((pair-pre (preWhisker in₁) (preWhisker in₂) (decode⁼-functor x y)) ⁻¹)
            (pair-squares-isEquiv (decode-pre in₁ x) (decode-pre in₁ y)
              (decode-pre in₂ x) (decode-pre in₂ y)
              (D₁ ∘ postWhisker F) (D₂ ∘ postWhisker G)
              (preWhisker in₁ ∘ decode⁼-functor x y) (preWhisker in₂ ∘ decode⁼-functor x y)
              (decode-pre-square in₁ x y) (decode-pre-square in₂ x y)
              (pair-post-isEquiv D₁ D₂ (postWhisker F) (postWhisker G)
                (decode⁼-isEquiv (F ∘ x) (F ∘ y)) (decode⁼-isEquiv (G ∘ x) (G ∘ y))
                (paired-postWhisker-isEquiv F G (coproductRestriction-isEquiv C D E) x y))))
        where
        F : MAP (Map (C ⊔ D) E) (Map C E)
        F = mapPre (in₁ {C = C} {D = D})
        G : MAP (Map (C ⊔ D) E) (Map D E)
        G = mapPre (in₂ {C = C} {D = D})
        D₁ : MAP (Equal (F ∘ x) (F ∘ y)) (Equal (decode (F ∘ x)) (decode (F ∘ y)))
        D₁ = decode⁼-functor (F ∘ x) (F ∘ y)
        D₂ : MAP (Equal (G ∘ x) (G ∘ y)) (Equal (decode (G ∘ x)) (decode (G ∘ y)))
        D₂ = decode⁼-functor (G ∘ x) (G ∘ y)

  coproductRestriction₌-isEquiv : {C D E : CAT Γ} (h k : MAP (C ⊔ D) E)
    → IsEquiv (coproductRestriction₌ h k)
  coproductRestriction₌-isEquiv h k =
    equiv-cancel-right change (coproductRestriction₌ h k)
      (changeEndpoints₌-isEquiv p q)
      (equiv-transport ((pair-pre (preWhisker in₁) (preWhisker in₂) change) ⁻¹)
        (pair-squares-isEquiv (p ▷ in₁) (q ▷ in₁) (p ▷ in₂) (q ▷ in₂)
          (preWhisker in₁) (preWhisker in₂) (preWhisker in₁ ∘ change) (preWhisker in₂ ∘ change)
          (preWhisker-changeEndpoints-square in₁ p q) (preWhisker-changeEndpoints-square in₂ p q)
          (decoded-restriction-isEquiv (name h) (name k))))
    where
    p : decode (name h) =₁ h
    p = decode-name h
    q : decode (name k) =₁ k
    q = decode-name k
    change : MAP (Equal (decode (name h)) (decode (name k))) (Equal h k)
    change = changeEndpoints₌ p q
```

## Prescribed restrictions

The family parameter is independent of the coproduct source. The existing
Factorization view supplies the chosen recovered family and its full
restriction triangle. Both projected laws compare families, so their
equalities are =₁. At One they have the individual =₂ signatures.
This choice is distinct from the private preliminary reflection used by
the copair laws; no agreement between those choices is assumed.

```agda
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    module IdentificationFromRestrictions {C D E : CAT Γ} (h k : MAP (C ⊔ D) E)
      (α : (h ∘ in₁) ＝ (k ∘ in₁)) (β : (h ∘ in₂) ＝ (k ∘ in₂)) where

      chosen : Factorization (coproductRestriction₌ h k) (pair α β)
      chosen = factor-through-equiv (coproductRestriction₌-isEquiv h k) (pair α β)

      identification : h ＝ k
      identification = factor chosen

      restriction-law : (coproductRestriction₌ h k ∘ identification) =₁ pair α β
      restriction-law = triangle chosen

      restriction₁ : (identification ▷ in₁) =₁ α
      restriction₁ = pair-β₁ α β ∙ ((pr₁ ◁ restriction-law) ∙
        (project-pair₁ (preWhisker in₁) (preWhisker in₂) identification) ⁻¹)

      restriction₂ : (identification ▷ in₂) =₁ β
      restriction₂ = pair-β₂ α β ∙ ((pr₂ ◁ restriction-law) ∙
        (project-pair₂ (preWhisker in₁) (preWhisker in₂) identification) ⁻¹)
```
