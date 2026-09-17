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
    (P : NatIso a₂ a₃) (A : NatIso a₁ a₂) (B : NatIso a₀ a₁)
    (B⁻ : NatIso a₁ a₀) → Iso₂ B⁻ (invIso B) →
    Iso₂ ((P ∙ (A ∙ B)) ∙ (B⁻ ∙ invIso A)) P
  cancel-trailing-pair P A B B⁻ inverse = cancel-right A P ∙
    (isoComp-cong
      (cancel-right B (P ∙ A) ∙ isoComp-cong (idIso ((P ∙ A) ∙ B)) inverse)
      (idIso (invIso A)) ∙
    (invIso (isoComp-assoc-at ((P ∙ A) ∙ B) B⁻ (invIso A)) ∙
      isoComp-cong (invIso (isoComp-assoc-at P A B)) (idIso (B⁻ ∙ invIso A))))

  prefix-transfer : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (L : NatIso a₃ a₄) (T : NatIso a₂ a₃) (D : NatIso a₂ a₄)
    (P : NatIso a₁ a₂) (z : NatIso a₀ a₁) (q : NatIso a₅ a₃) (u : NatIso a₀ a₅) →
    Iso₂ D (L ∙ T) → Iso₂ ((T ∙ P) ∙ z) (q ∙ u) →
    Iso₂ ((D ∙ P) ∙ z) ((L ∙ q) ∙ u)
  prefix-transfer L T D P z q u endpoint core = invIso (isoComp-assoc-at L q u) ∙
    (isoComp-cong (idIso L) core ∙
    (isoComp-assoc-at L (T ∙ P) z ∙
    (isoComp-cong (isoComp-assoc-at L T P) (idIso z) ∙
      isoComp-cong (isoComp-cong endpoint (idIso P)) (idIso z))))

  cancel-prefix : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
    (O : NatIso a₄ a₅) (S : NatIso a₃ a₄) (A : NatIso a₂ a₃)
    (K : NatIso a₁ a₃) (P : NatIso a₀ a₁) (Q : NatIso a₀ a₄) →
    Iso₂ (S ∙ (K ∙ P)) Q →
    Iso₂ ((O ∙ (S ∙ A)) ∙ ((invIso A ∙ K) ∙ P)) (O ∙ Q)
  cancel-prefix O S A K P Q square = isoComp-cong (idIso O) square ∙
    (isoComp-cong (idIso O) (isoComp-cong (idIso S) (cancel-inverse A (K ∙ P))) ∙
    (isoComp-cong (idIso O) (isoComp-cong (idIso S)
      (isoComp-cong (idIso A) (isoComp-assoc-at (invIso A) K P))) ∙
    (isoComp-cong (idIso O) (isoComp-assoc-at S A ((invIso A ∙ K) ∙ P)) ∙
      isoComp-assoc-at O (S ∙ A) ((invIso A ∙ K) ∙ P))))

  close-comparison : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
    (source : NatIso a₀ a₄) (prefix : NatIso a₃ a₄)
    (D : NatIso a₂ a₃) (P : NatIso a₁ a₂) (z : NatIso a₀ a₁)
    (seed : NatIso a₀ a₃) (boundary : NatIso a₁ a₄) (result : NatIso a₀ a₄) →
    Iso₂ source (prefix ∙ seed) → Iso₂ ((D ∙ P) ∙ z) seed →
    Iso₂ (prefix ∙ (D ∙ P)) boundary → Iso₂ (boundary ∙ z) result →
    Iso₂ source result
  close-comparison source prefix D P z seed boundary result start transfer remove finish = finish ∙
    (isoComp-cong remove (idIso z) ∙
    (invIso (isoComp-assoc-at prefix (D ∙ P) z) ∙
    (isoComp-cong (idIso prefix) (invIso transfer) ∙ start)))

module Boundary {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
  (A : NatIso a₁ a₂) (B : NatIso a₀ a₁) (C : NatIso a₄ a₃)
  (S : NatIso a₂ a₃) (B⁻ : NatIso a₁ a₀) (S⁻ : NatIso a₃ a₂)
  (I : NatIso a₄ a₄)
  (inverse-B : Iso₂ B⁻ (invIso B)) (inverse-S : Iso₂ S⁻ (invIso S))
  (identity-I : Iso₂ I (idIso a₄)) where

  comparison = invIso C ∙ (S ∙ (A ∙ B))
  source = B⁻ ∙ invIso A
  target = I ∙ invIso C

  abstract
    cancel-source : Iso₂ (comparison ∙ source) (invIso C ∙ S)
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

    cancel-target : Iso₂ (target ∙ S) (invIso C ∙ S)
    cancel-target = isoComp-cong
      (isoComp-unitˡ-at (invIso C) ∙ isoComp-cong identity-I (idIso (invIso C)))
      (idIso S)

    inverse-square : Iso₂ (source ∙ S⁻) (invIso comparison ∙ target)
    inverse-square = invIso
      (move-square comparison source target S (invIso cancel-target ∙ cancel-source)) ∙
      isoComp-cong (idIso source) inverse-S
```
