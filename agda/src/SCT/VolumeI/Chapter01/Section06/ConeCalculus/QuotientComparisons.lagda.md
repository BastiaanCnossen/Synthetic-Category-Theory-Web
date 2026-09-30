# Cone comparisons from a framed matching equation

An evaluated cone often has matching given by a quotient of its endpoint
frames. A single square for those frames supplies a comparison of whole
cones, with the prescribed leg identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.QuotientComparisons
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

abstract
  nested-quotient-square : {Γ Z : CAT} {h k l v w z : MAP Γ Z}
    (L : h =₁ l) (ω : l =₁ v) (δ : v =₁ w) (A : z =₁ w) (R : k =₁ z) →
    ((A ∙ R) ∙ (R ⁻¹ ∙ ((A ⁻¹ ∙ (δ ∙ ω)) ∙ L))) =₂ (δ ∙ (ω ∙ L))
  nested-quotient-square L ω δ A R = isoComp-assoc-at δ ω L ∙
    (isoComp-cong (cancel-inverse A (δ ∙ ω)) (idIso L) ∙
    ((isoComp-assoc-at A (A ⁻¹ ∙ (δ ∙ ω)) L) ⁻¹ ∙
    (isoComp-cong (idIso A) (cancel-inverse R ((A ⁻¹ ∙ (δ ∙ ω)) ∙ L)) ∙
      isoComp-assoc-at A R (R ⁻¹ ∙ ((A ⁻¹ ∙ (δ ∙ ω)) ∙ L)))))

quotient-comparison : {A B Z Γ : CAT} (f : MAP A Z) (g : MAP B Z)
  {a a′ : MAP Γ A} {b b′ : MAP Γ B} {h k : MAP Γ Z}
  (α : a =₁ a′) (β : b =₁ b′)
  (L : h =₁ (f ∘ a)) (R : k =₁ (g ∘ b)) (τ : h =₁ k)
  (δ : (f ∘ a′) =₁ (g ∘ b′)) →
  (((g ◁ β) ∙ R) ∙ τ) =₂ (δ ∙ ((f ◁ α) ∙ L)) →
  ConeIso
    (record { left = a ; right = b ; match = R ∙ (τ ∙ L ⁻¹) })
    (record { left = a′ ; right = b′ ; match = δ })
quotient-comparison f g α β L R τ δ square = record
  { leftIso = α ; rightIso = β ; compatible = law }
  where
  abstract
    law : (δ ∙ (f ◁ α)) =₂ ((g ◁ β) ∙ (R ∙ (τ ∙ L ⁻¹)))
    law =
      isoComp-cong (idIso (g ◁ β)) (isoComp-assoc-at R τ (L ⁻¹)) ∙
      (isoComp-assoc-at (g ◁ β) (R ∙ τ) (L ⁻¹) ∙
      (isoComp-cong (isoComp-assoc-at (g ◁ β) R τ) (idIso (L ⁻¹)) ∙
      (isoComp-cong (square ⁻¹) (idIso (L ⁻¹)) ∙
      (isoComp-cong (isoComp-assoc-at δ (f ◁ α) L) (idIso (L ⁻¹)) ∙
      (cancel-right L (δ ∙ (f ◁ α))) ⁻¹))))
```
