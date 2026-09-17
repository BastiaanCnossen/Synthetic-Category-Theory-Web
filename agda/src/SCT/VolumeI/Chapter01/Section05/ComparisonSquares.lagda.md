# Algebra for comparison squares

These calculations apply a functor to a specified square, form quotients,
and transport its boundaries. They also apply one dimension higher,
inside an isomorphism anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section05.ComparisonSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right; cancel-left)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (inverse-inverse)

post-square : {X Y Z : CAT} (F : MAP Y Z)
  {a a′ b b′ : MAP X Y}
  (u : NatIso a b) (u′ : NatIso a′ b′)
  (α : NatIso a a′) (β : NatIso b b′)
  → Iso₂ (u′ ∙ α) (β ∙ u)
  → Iso₂ ((F ◁ u′) ∙ (F ◁ α)) ((F ◁ β) ∙ (F ◁ u))
post-square F u u′ α β p = postWhisker-isoComp-at F β u ∙
  ((postWhisker F ◁ p) ∙ invIso (postWhisker-isoComp-at F u′ α))

quotient-square : {X Y : CAT} {x x′ y y′ z z′ : MAP X Y}
  (α : NatIso x z) (β : NatIso y z) (α′ : NatIso x′ z′) (β′ : NatIso y′ z′)
  (L : NatIso x x′) (R : NatIso y y′) (V : NatIso z z′)
  → Iso₂ (α′ ∙ L) (V ∙ α) → Iso₂ (β′ ∙ R) (V ∙ β)
  → Iso₂ ((invIso β′ ∙ α′) ∙ L) (R ∙ (invIso β ∙ α))
quotient-square α β α′ β′ L R V first second =
  isoComp-assoc-at R (invIso β) α ∙
  (isoComp-cong (move-square β′ R V β second) (idIso α) ∙
  (invIso (isoComp-assoc-at (invIso β′) V α) ∙
  (isoComp-cong (idIso (invIso β′)) first ∙ isoComp-assoc-at (invIso β′) α′ L)))

normalize-cone-square : {X Y : CAT} {x x′ y y′ u v : MAP X Y}
  (A : NatIso x x′) (B : NatIso y y′) (q : NatIso x y) (q′ : NatIso u v)
  (L : NatIso u x′) (R : NatIso v y′)
  → Iso₂ (q ∙ (invIso A ∙ L)) ((invIso B ∙ R) ∙ q′)
  → Iso₂ ((B ∙ (q ∙ invIso A)) ∙ L) (R ∙ q′)
normalize-cone-square A B q q′ L R square = cancel-inverse B (R ∙ q′) ∙
  (isoComp-cong (idIso B) (isoComp-assoc-at (invIso B) R q′) ∙
  (isoComp-cong (idIso B) square ∙
  (isoComp-cong (idIso B) (isoComp-assoc-at q (invIso A) L) ∙
    isoComp-assoc-at B (q ∙ invIso A) L)))

transport-square : {X Y : CAT} {a₀ a₁ b₀ b₁ x₀ x₁ y₀ y₁ : MAP X Y}
  (L₀ : NatIso a₀ x₀) (L₁ : NatIso a₁ x₁)
  (R₀ : NatIso b₀ y₀) (R₁ : NatIso b₁ y₁)
  (q₀ : NatIso a₀ b₀) (q₁ : NatIso a₁ b₁)
  (u : NatIso a₀ a₁) (v : NatIso b₀ b₁)
  (α : NatIso x₀ x₁) (β : NatIso y₀ y₁)
  → Iso₂ (L₁ ∙ u) (α ∙ L₀) → Iso₂ (R₁ ∙ v) (β ∙ R₀)
  → Iso₂ (q₁ ∙ u) (v ∙ q₀)
  → Iso₂ ((R₁ ∙ (q₁ ∙ invIso L₁)) ∙ α)
      (β ∙ (R₀ ∙ (q₀ ∙ invIso L₀)))
transport-square L₀ L₁ R₀ R₁ q₀ q₁ u v α β left right middle =
  paste-squares (q₀ ∙ invIso L₀) (q₁ ∙ invIso L₁) R₀ R₁ α v β
    (paste-squares (invIso L₀) (invIso L₁) q₀ q₁ α u v
      (move-square L₁ u α L₀ left) middle) right

decode-encode : {X Y : CAT} {a b x y : MAP X Y}
  (L : NatIso a x) (R : NatIso b y) (γ : NatIso x y)
  → Iso₂ (R ∙ ((invIso R ∙ (γ ∙ L)) ∙ invIso L)) γ
decode-encode L R γ = cancel-right L γ ∙
  (isoComp-cong (cancel-inverse R (γ ∙ L)) (idIso (invIso L)) ∙
    invIso (isoComp-assoc-at R (invIso R ∙ (γ ∙ L)) (invIso L)))

untransport : {X Y : CAT} {a b x y : MAP X Y}
  (L : NatIso a x) (R : NatIso b y) (q : NatIso a b)
  → Iso₂ (invIso R ∙ ((R ∙ (q ∙ invIso L)) ∙ L)) q
untransport L R q = isoComp-unitʳ-at q ∙
  (isoComp-cong (idIso q) (isoComp-inverseˡ-at L) ∙
  (isoComp-assoc-at q (invIso L) L ∙
  (isoComp-cong (cancel-left R (q ∙ invIso L)) (idIso L) ∙
    invIso (isoComp-assoc-at (invIso R) (R ∙ (q ∙ invIso L)) L))))

reflect-transport-square : {X Y : CAT} {a₀ a₁ b₀ b₁ x₀ x₁ y₀ y₁ : MAP X Y}
  (L₀ : NatIso a₀ x₀) (L₁ : NatIso a₁ x₁)
  (R₀ : NatIso b₀ y₀) (R₁ : NatIso b₁ y₁)
  (q₀ : NatIso a₀ b₀) (q₁ : NatIso a₁ b₁)
  (u : NatIso a₀ a₁) (v : NatIso b₀ b₁)
  (α : NatIso x₀ x₁) (β : NatIso y₀ y₁)
  → Iso₂ (L₁ ∙ u) (α ∙ L₀) → Iso₂ (R₁ ∙ v) (β ∙ R₀)
  → Iso₂ ((R₁ ∙ (q₁ ∙ invIso L₁)) ∙ α)
      (β ∙ (R₀ ∙ (q₀ ∙ invIso L₀)))
  → Iso₂ (q₁ ∙ u) (v ∙ q₀)
reflect-transport-square L₀ L₁ R₀ R₁ q₀ q₁ u v α β left right middle =
  isoComp-cong (idIso v) (normalize L₀ R₀ q₀) ∙
  (transport-square (invIso L₀) (invIso L₁) (invIso R₀) (invIso R₁)
    (R₀ ∙ (q₀ ∙ invIso L₀)) (R₁ ∙ (q₁ ∙ invIso L₁)) α β u v
    (move-square L₁ u α L₀ left) (move-square R₁ v β R₀ right) middle ∙
    isoComp-cong (invIso (normalize L₁ R₁ q₁)) (idIso u))
  where
  normalize : ∀ {a b x y} (L : NatIso a x) (R : NatIso b y) (q : NatIso a b)
    → Iso₂ (invIso R ∙ ((R ∙ (q ∙ invIso L)) ∙ invIso (invIso L))) q
  normalize L R q = untransport L R q ∙
    isoComp-cong (idIso (invIso R))
      (isoComp-cong (idIso (R ∙ (q ∙ invIso L))) (inverse-inverse L))

encoded-restriction-square : {X Y : CAT} {a a′ b b′ x y : MAP X Y}
  (A : NatIso a a′) (B : NatIso b b′)
  (u : NatIso a′ x) (v : NatIso b′ y) (δ : NatIso x y) (r : NatIso a b)
  → Iso₂ r (invIso (v ∙ B) ∙ (δ ∙ (u ∙ A)))
  → Iso₂ (δ ∙ u) (v ∙ (B ∙ (r ∙ invIso A)))
encoded-restriction-square A B u v δ r image =
  isoComp-assoc-at v B (r ∙ invIso A) ∙
  (isoComp-assoc-at (v ∙ B) r (invIso A) ∙
  (isoComp-cong square (idIso (invIso A)) ∙
  (isoComp-cong (isoComp-assoc-at δ u A) (idIso (invIso A)) ∙
    invIso (cancel-right A (δ ∙ u)))))
  where
  square : Iso₂ (δ ∙ (u ∙ A)) ((v ∙ B) ∙ r)
  square = isoComp-cong (idIso (v ∙ B)) (invIso image) ∙
    invIso (cancel-inverse (v ∙ B) (δ ∙ (u ∙ A)))
```
