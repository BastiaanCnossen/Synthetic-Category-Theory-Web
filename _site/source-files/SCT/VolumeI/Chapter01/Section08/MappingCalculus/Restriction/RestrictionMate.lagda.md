# Cancelling a restriction comparison

A restriction comparison consists of a square between two associators.
This elementary calculation reverses that square while retaining its
chosen inverse and identity comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.RestrictionMate
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; move-square)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

abstract
  cancel-trailing-pair : {X Y : CAT} {a₀ a₁ a₂ a₃ : MAP X Y}
    (P : a₂ =₁ a₃) (A : a₁ =₁ a₂) (B : a₀ =₁ a₁)
    (B⁻ : a₁ =₁ a₀) → B⁻ =₂ (B ⁻¹) →
    ((P ∙ (A ∙ B)) ∙ (B⁻ ∙ A ⁻¹)) =₂ P
  cancel-trailing-pair P A B B⁻ inverse = cancel-right A P ∙
    (isoComp-cong
      (cancel-right B (P ∙ A) ∙ isoComp-cong (idIso ((P ∙ A) ∙ B)) inverse)
      (idIso (A ⁻¹)) ∙
    ((isoComp-assoc-at ((P ∙ A) ∙ B) B⁻ (A ⁻¹)) ⁻¹ ∙
      isoComp-cong ((isoComp-assoc-at P A B) ⁻¹) (idIso (B⁻ ∙ A ⁻¹))))

  prefix-transfer : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (L : a₃ =₁ a₄) (T : a₂ =₁ a₃) (D : a₂ =₁ a₄)
    (P : a₁ =₁ a₂) (z : a₀ =₁ a₁) (q : a₅ =₁ a₃) (u : a₀ =₁ a₅) →
    D =₂ (L ∙ T) → ((T ∙ P) ∙ z) =₂ (q ∙ u) →
    ((D ∙ P) ∙ z) =₂ ((L ∙ q) ∙ u)
  prefix-transfer L T D P z q u endpoint core = (isoComp-assoc-at L q u) ⁻¹ ∙
    (isoComp-cong (idIso L) core ∙
    (isoComp-assoc-at L (T ∙ P) z ∙
    (isoComp-cong (isoComp-assoc-at L T P) (idIso z) ∙
      isoComp-cong (isoComp-cong endpoint (idIso P)) (idIso z))))

  cancel-prefix : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (O : a₄ =₁ a₅) (S : a₃ =₁ a₄) (A : a₂ =₁ a₃)
    (K : a₁ =₁ a₃) (P : a₀ =₁ a₁) (Q : a₀ =₁ a₄) →
    (S ∙ (K ∙ P)) =₂ Q →
    ((O ∙ (S ∙ A)) ∙ ((A ⁻¹ ∙ K) ∙ P)) =₂ (O ∙ Q)
  cancel-prefix O S A K P Q square = isoComp-cong (idIso O) square ∙
    (isoComp-cong (idIso O) (isoComp-cong (idIso S) (cancel-inverse A (K ∙ P))) ∙
    (isoComp-cong (idIso O) (isoComp-cong (idIso S)
      (isoComp-cong (idIso A) (isoComp-assoc-at (A ⁻¹) K P))) ∙
    (isoComp-cong (idIso O) (isoComp-assoc-at S A ((A ⁻¹ ∙ K) ∙ P)) ∙
      isoComp-assoc-at O (S ∙ A) ((A ⁻¹ ∙ K) ∙ P))))

  close-comparison : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (source : a₀ =₁ a₄) (prefix : a₃ =₁ a₄)
    (D : a₂ =₁ a₃) (P : a₁ =₁ a₂) (z : a₀ =₁ a₁)
    (seed : a₀ =₁ a₃) (boundary : a₁ =₁ a₄) (result : a₀ =₁ a₄) →
    source =₂ (prefix ∙ seed) → ((D ∙ P) ∙ z) =₂ seed →
    (prefix ∙ (D ∙ P)) =₂ boundary → (boundary ∙ z) =₂ result →
    source =₂ result
  close-comparison source prefix D P z seed boundary result start transfer remove finish = finish ∙
    (isoComp-cong remove (idIso z) ∙
    ((isoComp-assoc-at prefix (D ∙ P) z) ⁻¹ ∙
    (isoComp-cong (idIso prefix) (transfer ⁻¹) ∙ start)))

module Boundary {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
  (A : a₁ =₁ a₂) (B : a₀ =₁ a₁) (C : a₄ =₁ a₃)
  (S : a₂ =₁ a₃) (B⁻ : a₁ =₁ a₀) (S⁻ : a₃ =₁ a₂)
  (I : a₄ =₁ a₄)
  (inverse-B : B⁻ =₂ (B ⁻¹)) (inverse-S : S⁻ =₂ (S ⁻¹))
  (identity-I : I =₂ (idIso a₄)) where

  comparison = C ⁻¹ ∙ (S ∙ (A ∙ B))
  source = B⁻ ∙ A ⁻¹
  target = I ∙ C ⁻¹

  abstract
    cancel-source : (comparison ∙ source) =₂ (C ⁻¹ ∙ S)
    cancel-source = cancel-right A (C ⁻¹ ∙ S) ∙
      (isoComp-cong
        (cancel-right B ((C ⁻¹ ∙ S) ∙ A) ∙
          isoComp-cong (idIso (((C ⁻¹ ∙ S) ∙ A) ∙ B)) inverse-B)
        (idIso (A ⁻¹)) ∙
      ((isoComp-assoc-at (((C ⁻¹ ∙ S) ∙ A) ∙ B) B⁻ (A ⁻¹)) ⁻¹ ∙
        isoComp-cong
          ((isoComp-assoc-at (C ⁻¹ ∙ S) A B) ⁻¹ ∙
            (isoComp-assoc-at (C ⁻¹) S (A ∙ B)) ⁻¹)
          (idIso source)))

    cancel-target : (target ∙ S) =₂ (C ⁻¹ ∙ S)
    cancel-target = isoComp-cong
      (isoComp-unitˡ-at (C ⁻¹) ∙ isoComp-cong identity-I (idIso (C ⁻¹)))
      (idIso S)

    inverse-square : (source ∙ S⁻) =₂ (comparison ⁻¹ ∙ target)
    inverse-square =
      (move-square comparison source target S (cancel-target ⁻¹ ∙ cancel-source)) ⁻¹ ∙
      isoComp-cong (idIso source) inverse-S
```
