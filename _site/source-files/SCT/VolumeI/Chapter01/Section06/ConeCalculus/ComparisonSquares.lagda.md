# Algebra for comparison squares

These calculations apply a functor to a specified square, form quotients,
and transport its boundaries. They also apply one dimension higher,
inside an isomorphism anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right; cancel-left)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)

post-square : {X Y Z : CAT} (F : MAP Y Z)
  {a a′ b b′ : MAP X Y}
  (u : a =₁ b) (u′ : a′ =₁ b′)
  (α : a =₁ a′) (β : b =₁ b′)
  → (u′ ∙ α) =₂ (β ∙ u)
  → ((F ◁ u′) ∙ (F ◁ α)) =₂ ((F ◁ β) ∙ (F ◁ u))
post-square F u u′ α β p = postWhisker-isoComp-at F β u ∙
  ((postWhisker F ◁ p) ∙ (postWhisker-isoComp-at F u′ α) ⁻¹)

quotient-square : {X Y : CAT} {x x′ y y′ z z′ : MAP X Y}
  (α : x =₁ z) (β : y =₁ z) (α′ : x′ =₁ z′) (β′ : y′ =₁ z′)
  (L : x =₁ x′) (R : y =₁ y′) (V : z =₁ z′)
  → (α′ ∙ L) =₂ (V ∙ α) → (β′ ∙ R) =₂ (V ∙ β)
  → ((β′ ⁻¹ ∙ α′) ∙ L) =₂ (R ∙ (β ⁻¹ ∙ α))
quotient-square α β α′ β′ L R V first second =
  isoComp-assoc-at R (β ⁻¹) α ∙
  (isoComp-cong (move-square β′ R V β second) (idIso α) ∙
  ((isoComp-assoc-at (β′ ⁻¹) V α) ⁻¹ ∙
  (isoComp-cong (idIso (β′ ⁻¹)) first ∙ isoComp-assoc-at (β′ ⁻¹) α′ L)))

normalize-cone-square : {X Y : CAT} {x x′ y y′ u v : MAP X Y}
  (A : x =₁ x′) (B : y =₁ y′) (q : x =₁ y) (q′ : u =₁ v)
  (L : u =₁ x′) (R : v =₁ y′)
  → (q ∙ (A ⁻¹ ∙ L)) =₂ ((B ⁻¹ ∙ R) ∙ q′)
  → ((B ∙ (q ∙ A ⁻¹)) ∙ L) =₂ (R ∙ q′)
normalize-cone-square A B q q′ L R square = cancel-inverse B (R ∙ q′) ∙
  (isoComp-cong (idIso B) (isoComp-assoc-at (B ⁻¹) R q′) ∙
  (isoComp-cong (idIso B) square ∙
  (isoComp-cong (idIso B) (isoComp-assoc-at q (A ⁻¹) L) ∙
    isoComp-assoc-at B (q ∙ A ⁻¹) L)))

transport-square : {X Y : CAT} {a₀ a₁ b₀ b₁ x₀ x₁ y₀ y₁ : MAP X Y}
  (L₀ : a₀ =₁ x₀) (L₁ : a₁ =₁ x₁)
  (R₀ : b₀ =₁ y₀) (R₁ : b₁ =₁ y₁)
  (q₀ : a₀ =₁ b₀) (q₁ : a₁ =₁ b₁)
  (u : a₀ =₁ a₁) (v : b₀ =₁ b₁)
  (α : x₀ =₁ x₁) (β : y₀ =₁ y₁)
  → (L₁ ∙ u) =₂ (α ∙ L₀) → (R₁ ∙ v) =₂ (β ∙ R₀)
  → (q₁ ∙ u) =₂ (v ∙ q₀)
  → ((R₁ ∙ (q₁ ∙ L₁ ⁻¹)) ∙ α) =₂
      (β ∙ (R₀ ∙ (q₀ ∙ L₀ ⁻¹)))
transport-square L₀ L₁ R₀ R₁ q₀ q₁ u v α β left right middle =
  paste-squares (q₀ ∙ L₀ ⁻¹) (q₁ ∙ L₁ ⁻¹) R₀ R₁ α v β
    (paste-squares (L₀ ⁻¹) (L₁ ⁻¹) q₀ q₁ α u v
      (move-square L₁ u α L₀ left) middle) right

decode-encode : {X Y : CAT} {a b x y : MAP X Y}
  (L : a =₁ x) (R : b =₁ y) (γ : x =₁ y)
  → (R ∙ ((R ⁻¹ ∙ (γ ∙ L)) ∙ L ⁻¹)) =₂ γ
decode-encode L R γ = cancel-right L γ ∙
  (isoComp-cong (cancel-inverse R (γ ∙ L)) (idIso (L ⁻¹)) ∙
    (isoComp-assoc-at R (R ⁻¹ ∙ (γ ∙ L)) (L ⁻¹)) ⁻¹)

untransport : {X Y : CAT} {a b x y : MAP X Y}
  (L : a =₁ x) (R : b =₁ y) (q : a =₁ b)
  → (R ⁻¹ ∙ ((R ∙ (q ∙ L ⁻¹)) ∙ L)) =₂ q
untransport L R q = isoComp-unitʳ-at q ∙
  (isoComp-cong (idIso q) (isoComp-inverseˡ-at L) ∙
  (isoComp-assoc-at q (L ⁻¹) L ∙
  (isoComp-cong (cancel-left R (q ∙ L ⁻¹)) (idIso L) ∙
    (isoComp-assoc-at (R ⁻¹) (R ∙ (q ∙ L ⁻¹)) L) ⁻¹)))

reflect-transport-square : {X Y : CAT} {a₀ a₁ b₀ b₁ x₀ x₁ y₀ y₁ : MAP X Y}
  (L₀ : a₀ =₁ x₀) (L₁ : a₁ =₁ x₁)
  (R₀ : b₀ =₁ y₀) (R₁ : b₁ =₁ y₁)
  (q₀ : a₀ =₁ b₀) (q₁ : a₁ =₁ b₁)
  (u : a₀ =₁ a₁) (v : b₀ =₁ b₁)
  (α : x₀ =₁ x₁) (β : y₀ =₁ y₁)
  → (L₁ ∙ u) =₂ (α ∙ L₀) → (R₁ ∙ v) =₂ (β ∙ R₀)
  → ((R₁ ∙ (q₁ ∙ L₁ ⁻¹)) ∙ α) =₂
      (β ∙ (R₀ ∙ (q₀ ∙ L₀ ⁻¹)))
  → (q₁ ∙ u) =₂ (v ∙ q₀)
reflect-transport-square L₀ L₁ R₀ R₁ q₀ q₁ u v α β left right middle =
  isoComp-cong (idIso v) (normalize L₀ R₀ q₀) ∙
  (transport-square (L₀ ⁻¹) (L₁ ⁻¹) (R₀ ⁻¹) (R₁ ⁻¹)
    (R₀ ∙ (q₀ ∙ L₀ ⁻¹)) (R₁ ∙ (q₁ ∙ L₁ ⁻¹)) α β u v
    (move-square L₁ u α L₀ left) (move-square R₁ v β R₀ right) middle ∙
    isoComp-cong ((normalize L₁ R₁ q₁) ⁻¹) (idIso u))
  where
  normalize : ∀ {a b x y} (L : a =₁ x) (R : b =₁ y) (q : a =₁ b)
    → (R ⁻¹ ∙ ((R ∙ (q ∙ L ⁻¹)) ∙ (L ⁻¹) ⁻¹)) =₂ q
  normalize L R q = untransport L R q ∙
    isoComp-cong (idIso (R ⁻¹))
      (isoComp-cong (idIso (R ∙ (q ∙ L ⁻¹))) (inverse-inverse L))

encoded-restriction-square : {X Y : CAT} {a a′ b b′ x y : MAP X Y}
  (A : a =₁ a′) (B : b =₁ b′)
  (u : a′ =₁ x) (v : b′ =₁ y) (δ : x =₁ y) (r : a =₁ b)
  → r =₂ ((v ∙ B) ⁻¹ ∙ (δ ∙ (u ∙ A)))
  → (δ ∙ u) =₂ (v ∙ (B ∙ (r ∙ A ⁻¹)))
encoded-restriction-square A B u v δ r image =
  isoComp-assoc-at v B (r ∙ A ⁻¹) ∙
  (isoComp-assoc-at (v ∙ B) r (A ⁻¹) ∙
  (isoComp-cong square (idIso (A ⁻¹)) ∙
  (isoComp-cong (isoComp-assoc-at δ u A) (idIso (A ⁻¹)) ∙
    (cancel-right A (δ ∙ u)) ⁻¹)))
  where
  square : (δ ∙ (u ∙ A)) =₂ ((v ∙ B) ∙ r)
  square = isoComp-cong (idIso (v ∙ B)) (image ⁻¹) ∙
    (cancel-inverse (v ∙ B) (δ ∙ (u ∙ A))) ⁻¹
```
