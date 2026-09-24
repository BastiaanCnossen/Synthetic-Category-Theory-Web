# Pasting corners through a common framed edge

Two endpoint cone comparisons sharing one edge determine a comparison
between their other edges. The equality of the common edge comparisons
is an explicit input. Cancelling that edge retains the two outer frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.FramedCornerPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EndpointFrameCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (coneIso-adjust; coneIso-swap)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-right)

abstract
  inverse-quotient : {X C : CAT} {x y z : MAP X C} (p : x =₁ z) (q : y =₁ z) →
    ((q ⁻¹ ∙ p) ⁻¹) =₂ (p ⁻¹ ∙ q)
  inverse-quotient p q = isoComp-cong (idIso (p ⁻¹)) (inverse-inverse q) ∙
    inverse-composite (q ⁻¹) p

  quotient-through : {X C : CAT} {x y z w : MAP X C}
    (p : x =₁ w) (q : y =₁ w) (r : z =₁ w) →
    ((r ⁻¹ ∙ p) ∙ (q ⁻¹ ∙ p) ⁻¹) =₂ (r ⁻¹ ∙ q)
  quotient-through p q r =
    isoComp-cong (cancel-right p (r ⁻¹)) (idIso q) ∙
    (isoComp-assoc-at (r ⁻¹ ∙ p) (p ⁻¹) q) ⁻¹ ∙
    isoComp-cong (idIso (r ⁻¹ ∙ p)) (inverse-quotient p q)

module ThroughCommon {Γ A B D C : CAT} {f : MAP A C} {g : MAP B C} {h : MAP D C}
  {l l′ : MAP Γ A} {m m′ : MAP Γ B} {n n′ : MAP Γ D} {z z′ : MAP Γ C}
  (p : (f ∘ l) =₁ z) (q : (g ∘ m) =₁ z) (r : (h ∘ n) =₁ z)
  (p′ : (f ∘ l′) =₁ z′) (q′ : (g ∘ m′) =₁ z′) (r′ : (h ∘ n′) =₁ z′)
  (Φ : ConeIso (framed-cone l m p q) (framed-cone l′ m′ p′ q′))
  (Ψ : ConeIso (framed-cone l n p r) (framed-cone l′ n′ p′ r′))
  (same : ConeIso.leftIso Ψ =₂ ConeIso.leftIso Φ) where
  adjusted = coneIso-adjust Ψ (ConeIso.leftIso Φ) (ConeIso.rightIso Ψ) same (idIso _)
  first = q ⁻¹ ∙ p
  second = r ⁻¹ ∙ p
  first′ = q′ ⁻¹ ∙ p′
  second′ = r′ ⁻¹ ∙ p′
  common = f ◁ ConeIso.leftIso Φ
  left = g ◁ ConeIso.rightIso Φ
  right = h ◁ ConeIso.rightIso Ψ

  comparison : ConeIso (framed-cone m n q r) (framed-cone m′ n′ q′ r′)
  comparison = record
    { leftIso = ConeIso.rightIso Φ ; rightIso = ConeIso.rightIso Ψ
    ; compatible = isoComp-cong (idIso right) (quotient-through p q r) ∙
        paste-squares (first ⁻¹) (first′ ⁻¹) second second′ left common right
          (move-square first′ common left first (ConeIso.compatible Φ))
          (ConeIso.compatible adjusted) ∙
        isoComp-cong ((quotient-through p′ q′ r′) ⁻¹) (idIso left) }

swap-framed : {Γ A B C : CAT} {f : MAP A C} {g : MAP B C}
  {l l′ : MAP Γ A} {r r′ : MAP Γ B} {z z′ : MAP Γ C}
  (p : (f ∘ l) =₁ z) (q : (g ∘ r) =₁ z)
  (p′ : (f ∘ l′) =₁ z′) (q′ : (g ∘ r′) =₁ z′) →
  ConeIso (framed-cone l r p q) (framed-cone l′ r′ p′ q′) →
  ConeIso (framed-cone r l q p) (framed-cone r′ l′ q′ p′)
swap-framed p q p′ q′ Φ = replace-matchings (coneIso-swap Φ) _ _
  (inverse-quotient p q) (inverse-quotient p′ q′)
```
