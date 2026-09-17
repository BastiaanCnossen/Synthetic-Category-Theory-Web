# Closing an evaluated square

The calculation below removes the endpoint comparisons from a commuting
evaluation diagram. It retains the resulting compatibility between the
two cocones. It is ordinary isomorphism calculus, independent of currying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.EvaluationSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯 using (encoded-restriction-square)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

append-five : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : MAP X Y}
  (A : NatIso a₅ a₆) (B : NatIso a₄ a₅) (C : NatIso a₃ a₄)
  (D : NatIso a₂ a₃) (E : NatIso a₁ a₂) (F : NatIso a₀ a₁) →
  Iso₂ ((A ∙ (B ∙ (C ∙ (D ∙ E)))) ∙ F)
    (A ∙ (B ∙ (C ∙ (D ∙ (E ∙ F)))))
append-five A B C D E F =
  isoComp-cong (idIso A) (isoComp-cong (idIso B) (isoComp-cong (idIso C) (isoComp-assoc-at D E F))) ∙
  (isoComp-cong (idIso A) (isoComp-cong (idIso B) (isoComp-assoc-at C (D ∙ E) F)) ∙
  (isoComp-cong (idIso A) (isoComp-assoc-at B (C ∙ (D ∙ E)) F) ∙
    isoComp-assoc-at A (B ∙ (C ∙ (D ∙ E))) F))

append-square : {X Y : CAT} {a₀ a₁ a₂ a₃ b : MAP X Y}
  (U : NatIso a₂ a₃) (V : NatIso a₁ a₂) (W : NatIso b a₃)
  (P : NatIso a₁ b) (z : NatIso a₀ a₁) →
  Iso₂ (U ∙ V) (W ∙ P) → Iso₂ (U ∙ (V ∙ z)) (W ∙ (P ∙ z))
append-square U V W P z square = isoComp-assoc-at W P z ∙
  (isoComp-cong square (idIso z) ∙ invIso (isoComp-assoc-at U V z))

compose-evaluated-pasting : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ b : MAP X Y}
  (W : NatIso a₄ a₅) (O : NatIso a₃ a₄) (A : NatIso a₂ a₃)
  (P : NatIso a₁ a₂) (Z : NatIso a₀ a₁) (T : NatIso a₂ a₅)
  (R : NatIso b a₅) (S : NatIso a₁ b) (U : NatIso a₀ b) →
  Iso₂ (W ∙ (O ∙ A)) T → Iso₂ (T ∙ P) (R ∙ S) → Iso₂ (S ∙ Z) U →
  Iso₂ (W ∙ (O ∙ (A ∙ (P ∙ Z)))) (R ∙ U)
compose-evaluated-pasting W O A P Z T R S U output pasted source =
  isoComp-cong (idIso R) source ∙
  (isoComp-assoc-at R S Z ∙
  (isoComp-cong pasted (idIso Z) ∙
  (invIso (isoComp-assoc-at T P Z) ∙
  (isoComp-cong output (idIso (P ∙ Z)) ∙
  (invIso (isoComp-assoc-at W (O ∙ A) (P ∙ Z)) ∙
    isoComp-cong (idIso W) (invIso (isoComp-assoc-at O A (P ∙ Z))))))))

cancel-evaluation-route : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
  (d : NatIso a₃ a₄) (c : NatIso a₂ a₃) (b : NatIso a₁ a₂) (a : NatIso a₀ a₁) →
  Iso₂ ((d ∙ (c ∙ (b ∙ a))) ∙ (invIso a ∙ (invIso b ∙ invIso c))) d
cancel-evaluation-route d c b a =
  isoComp-unitʳ-at d ∙
  (isoComp-cong (idIso d) (isoComp-inverseʳ-at c) ∙
  (isoComp-cong (idIso d) (isoComp-cong (idIso c) (cancel-inverse b (invIso c))) ∙
  (isoComp-cong (idIso d) (isoComp-cong (idIso c)
    (isoComp-cong (idIso b) (cancel-inverse a (invIso b ∙ invIso c)))) ∙
  (isoComp-cong (idIso d) (isoComp-cong (idIso c)
    (isoComp-assoc-at b a (invIso a ∙ (invIso b ∙ invIso c)))) ∙
  (isoComp-cong (idIso d) (isoComp-assoc-at c (b ∙ a) (invIso a ∙ (invIso b ∙ invIso c))) ∙
    isoComp-assoc-at d (c ∙ (b ∙ a)) (invIso a ∙ (invIso b ∙ invIso c)))))))
cancel-evaluation-pairs : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
  (a : NatIso a₁ a₂) (b : NatIso a₂ a₃) (c : NatIso a₃ a₄) (d : NatIso a₄ a₅)
  (u : NatIso a₀ a₁) →
  Iso₂ (((invIso a ∙ invIso b) ∙ (invIso c ∙ invIso d)) ∙
    (d ∙ (c ∙ (b ∙ (a ∙ u))))) u
cancel-evaluation-pairs a b c d u =
  cancel-left a u ∙
  (isoComp-cong (idIso (invIso a)) (cancel-left b (a ∙ u)) ∙
  (isoComp-assoc-at (invIso a) (invIso b) (b ∙ (a ∙ u)) ∙
  (isoComp-cong (idIso (invIso a ∙ invIso b))
    (cancel-left c (b ∙ (a ∙ u)) ∙
      (isoComp-cong (idIso (invIso c)) (cancel-left d (c ∙ (b ∙ (a ∙ u)))) ∙
        isoComp-assoc-at (invIso c) (invIso d) (d ∙ (c ∙ (b ∙ (a ∙ u)))))) ∙
    isoComp-assoc-at (invIso a ∙ invIso b) (invIso c ∙ invIso d)
      (d ∙ (c ∙ (b ∙ (a ∙ u)))))))
changeEndpoints-compose : {X Y : CAT} {a₀ a₁ a₂ b₀ b₁ b₂ : MAP X Y}
  (p : NatIso a₀ a₁) (q : NatIso a₁ a₂) (r : NatIso b₀ b₁) (s : NatIso b₁ b₂)
  (γ : NatIso a₀ b₀) →
  Iso₂ (changeEndpoints (q ∙ p) (s ∙ r) γ)
    (changeEndpoints q s (changeEndpoints p r γ))
changeEndpoints-compose p q r s γ =
  isoComp-cong (idIso s) (invIso (isoComp-assoc-at r (γ ∙ invIso p) (invIso q))) ∙
  (isoComp-cong (idIso s) (isoComp-cong (idIso r) (invIso (isoComp-assoc-at γ (invIso p) (invIso q)))) ∙
  (isoComp-assoc-at s r (γ ∙ (invIso p ∙ invIso q)) ∙
    isoComp-cong (idIso (s ∙ r)) (isoComp-cong (idIso γ) (inverse-composite q p))))

close-evaluation-square : {X Y : CAT} {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : MAP X Y}
  (A : NatIso a₀ a₁) (B : NatIso b₀ b₁)
  (L : NatIso a₁ a₂) (R : NatIso b₁ b₂)
  (a : NatIso a₂ a₃) (b : NatIso b₂ b₃)
  (γ : NatIso a₀ b₀) (δ : NatIso a₃ b₃) →
  Iso₂ (δ ∙ (a ∙ (L ∙ A))) ((b ∙ (R ∙ B)) ∙ γ) →
  Iso₂ ((invIso b ∙ (δ ∙ a)) ∙ L) (R ∙ changeEndpoints A B γ)
close-evaluation-square A B L R a b γ δ square =
  encoded-restriction-square A B L R target γ image
  where
  target = invIso b ∙ (δ ∙ a)
  compact : Iso₂ (target ∙ (L ∙ A)) ((R ∙ B) ∙ γ)
  compact = cancel-left b ((R ∙ B) ∙ γ) ∙
    (isoComp-cong (idIso (invIso b))
      (isoComp-assoc-at b (R ∙ B) γ ∙ square) ∙
    (isoComp-cong (idIso (invIso b)) (isoComp-assoc-at δ a (L ∙ A)) ∙
      isoComp-assoc-at (invIso b) (δ ∙ a) (L ∙ A)))
  image : Iso₂ γ (invIso (R ∙ B) ∙ (target ∙ (L ∙ A)))
  image = isoComp-cong (idIso (invIso (R ∙ B))) (invIso compact) ∙
    invIso (cancel-left (R ∙ B) γ)
```
