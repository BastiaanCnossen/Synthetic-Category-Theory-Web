# Cancelling a restriction comparison

A restriction comparison consists of a square between two associators.
This elementary calculation reverses that square while retaining its
chosen inverse and identity comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.RestrictionMate
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; move-square)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

abstract
  cancel-trailing-pair : {X Y : CAT} {a₀ a₁ a₂ a₃ : MAP X Y}
    (P : =₁ a₂ a₃) (A : =₁ a₁ a₂) (B : =₁ a₀ a₁)
    (B⁻ : =₁ a₁ a₀) → =₂ B⁻ (invIso B) →
    =₂ ((P ∙ (A ∙ B)) ∙ (B⁻ ∙ invIso A)) P
  cancel-trailing-pair P A B B⁻ inverse = cancel-right A P ∙
    (isoComp-cong
      (cancel-right B (P ∙ A) ∙ isoComp-cong (idIso ((P ∙ A) ∙ B)) inverse)
      (idIso (invIso A)) ∙
    (invIso (isoComp-assoc-at ((P ∙ A) ∙ B) B⁻ (invIso A)) ∙
      isoComp-cong (invIso (isoComp-assoc-at P A B)) (idIso (B⁻ ∙ invIso A))))

  prefix-transfer : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (L : =₁ a₃ a₄) (T : =₁ a₂ a₃) (D : =₁ a₂ a₄)
    (P : =₁ a₁ a₂) (z : =₁ a₀ a₁) (q : =₁ a₅ a₃) (u : =₁ a₀ a₅) →
    =₂ D (L ∙ T) → =₂ ((T ∙ P) ∙ z) (q ∙ u) →
    =₂ ((D ∙ P) ∙ z) ((L ∙ q) ∙ u)
  prefix-transfer L T D P z q u endpoint core = invIso (isoComp-assoc-at L q u) ∙
    (isoComp-cong (idIso L) core ∙
    (isoComp-assoc-at L (T ∙ P) z ∙
    (isoComp-cong (isoComp-assoc-at L T P) (idIso z) ∙
      isoComp-cong (isoComp-cong endpoint (idIso P)) (idIso z))))

  cancel-prefix : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (O : =₁ a₄ a₅) (S : =₁ a₃ a₄) (A : =₁ a₂ a₃)
    (K : =₁ a₁ a₃) (P : =₁ a₀ a₁) (Q : =₁ a₀ a₄) →
    =₂ (S ∙ (K ∙ P)) Q →
    =₂ ((O ∙ (S ∙ A)) ∙ ((invIso A ∙ K) ∙ P)) (O ∙ Q)
  cancel-prefix O S A K P Q square = isoComp-cong (idIso O) square ∙
    (isoComp-cong (idIso O) (isoComp-cong (idIso S) (cancel-inverse A (K ∙ P))) ∙
    (isoComp-cong (idIso O) (isoComp-cong (idIso S)
      (isoComp-cong (idIso A) (isoComp-assoc-at (invIso A) K P))) ∙
    (isoComp-cong (idIso O) (isoComp-assoc-at S A ((invIso A ∙ K) ∙ P)) ∙
      isoComp-assoc-at O (S ∙ A) ((invIso A ∙ K) ∙ P))))

  close-comparison : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (source : =₁ a₀ a₄) (prefix : =₁ a₃ a₄)
    (D : =₁ a₂ a₃) (P : =₁ a₁ a₂) (z : =₁ a₀ a₁)
    (seed : =₁ a₀ a₃) (boundary : =₁ a₁ a₄) (result : =₁ a₀ a₄) →
    =₂ source (prefix ∙ seed) → =₂ ((D ∙ P) ∙ z) seed →
    =₂ (prefix ∙ (D ∙ P)) boundary → =₂ (boundary ∙ z) result →
    =₂ source result
  close-comparison source prefix D P z seed boundary result start transfer remove finish = finish ∙
    (isoComp-cong remove (idIso z) ∙
    (invIso (isoComp-assoc-at prefix (D ∙ P) z) ∙
    (isoComp-cong (idIso prefix) (invIso transfer) ∙ start)))

module Boundary {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
  (A : =₁ a₁ a₂) (B : =₁ a₀ a₁) (C : =₁ a₄ a₃)
  (S : =₁ a₂ a₃) (B⁻ : =₁ a₁ a₀) (S⁻ : =₁ a₃ a₂)
  (I : =₁ a₄ a₄)
  (inverse-B : =₂ B⁻ (invIso B)) (inverse-S : =₂ S⁻ (invIso S))
  (identity-I : =₂ I (idIso a₄)) where

  comparison = invIso C ∙ (S ∙ (A ∙ B))
  source = B⁻ ∙ invIso A
  target = I ∙ invIso C

  abstract
    cancel-source : =₂ (comparison ∙ source) (invIso C ∙ S)
    cancel-source = cancel-right A (invIso C ∙ S) ∙
      (isoComp-cong
        (cancel-right B ((invIso C ∙ S) ∙ A) ∙
          isoComp-cong (idIso (((invIso C ∙ S) ∙ A) ∙ B)) inverse-B)
        (idIso (invIso A)) ∙
      (invIso (isoComp-assoc-at (((invIso C ∙ S) ∙ A) ∙ B) B⁻ (invIso A)) ∙
        isoComp-cong
          (invIso (isoComp-assoc-at (invIso C ∙ S) A B) ∙
            invIso (isoComp-assoc-at (invIso C) S (A ∙ B)))
          (idIso source)))

    cancel-target : =₂ (target ∙ S) (invIso C ∙ S)
    cancel-target = isoComp-cong
      (isoComp-unitˡ-at (invIso C) ∙ isoComp-cong identity-I (idIso (invIso C)))
      (idIso S)

    inverse-square : =₂ (source ∙ S⁻) (invIso comparison ∙ target)
    inverse-square = invIso
      (move-square comparison source target S (invIso cancel-target ∙ cancel-source)) ∙
      isoComp-cong (idIso source) inverse-S
```
