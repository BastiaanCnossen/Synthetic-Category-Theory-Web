# Changing the boundaries of a comparison

These two calculations describe a commuting square after changing its
endpoints. They apply to whole families of identifications, so they can
be used to construct a functor between comparison animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Param

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonAlgebra
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Param vocabulary terminal products productLaws composition vertical
  using (assoc; const-comp; const-cong; left-cancel; right-cancel)

opaque
  move-family : {A X Y : CAT} {x x′ y y′ : MAP X Y}
    (p : x =₁ x′) (q : y =₁ y′)
    (u : MAP A (x ＝ y)) (v : MAP A (x′ ＝ y′)) →
    (const q ∙ u) =₁ (v ∙ const p) →
    (u ∙ const (p ⁻¹)) =₁ (const (q ⁻¹) ∙ v)
  move-family p q u v square =
    isoComp-cong (idIso (const (q ⁻¹))) (right-cancel p v) ∙
    (assoc (const (q ⁻¹)) (v ∙ const p) (const (p ⁻¹)) ∙
    (isoComp-cong (isoComp-cong (idIso (const (q ⁻¹))) square) (idIso (const (p ⁻¹))) ∙
      isoComp-cong ((left-cancel q u) ⁻¹) (idIso (const (p ⁻¹)))))

  left-boundary : {A X Y : CAT} {x x′ y y′ z w : MAP X Y}
    (p : x =₁ x′) (q : y =₁ y′) (τ : y =₁ z) (κ : z =₁ w)
    (u : MAP A (x ＝ y)) (v : MAP A (x′ ＝ y′)) →
    (const q ∙ u) =₁ (v ∙ const p) →
    (const κ ∙ ((const τ ∙ u) ∙ const (p ⁻¹))) =₁
      (const (κ ∙ (τ ∙ q ⁻¹)) ∙ v)
  left-boundary p q τ κ u v square =
    isoComp-cong (const-comp κ (τ ∙ q ⁻¹) ∙
      isoComp-cong (idIso (const κ)) (const-comp τ (q ⁻¹))) (idIso v) ∙
    ((assoc (const κ) (const τ ∙ const (q ⁻¹)) v) ⁻¹ ∙
    isoComp-cong (idIso (const κ))
      ((assoc (const τ) (const (q ⁻¹)) v) ⁻¹ ∙
       (isoComp-cong (idIso (const τ)) (move-family p q u v square) ∙
         assoc (const τ) u (const (p ⁻¹)))))

  right-boundary : {A X Y : CAT} {x x′ y z w : MAP X Y}
    (p : x =₁ x′) (τ : x =₁ y) (κ : z =₁ w) (κ₀ : y =₁ w)
    (u : MAP A (y ＝ z)) → (const κ ∙ u) =₁ const κ₀ →
    (const κ ∙ ((u ∙ const τ) ∙ const (p ⁻¹))) =₁
      const (κ₀ ∙ (τ ∙ p ⁻¹))
  right-boundary p τ κ κ₀ u square =
    const-comp κ₀ (τ ∙ p ⁻¹) ∙
    (isoComp-cong square (const-comp τ (p ⁻¹)) ∙
    ((assoc (const κ) u (const τ ∙ const (p ⁻¹))) ⁻¹ ∙
      isoComp-cong (idIso (const κ)) (assoc u (const τ) (const (p ⁻¹)))))
```

