# Closing an evaluated square

The calculation below removes the endpoint comparisons from a commuting
evaluation diagram. It retains the resulting compatibility between the
two cocones. It is ordinary isomorphism calculus, independent of currying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.EvaluationSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯 using (encoded-restriction-square)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

append-five : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : MAP X Y}
  (A : a₅ =₁ a₆) (B : a₄ =₁ a₅) (C : a₃ =₁ a₄)
  (D : a₂ =₁ a₃) (E : a₁ =₁ a₂) (F : a₀ =₁ a₁) →
  ((A ∙ (B ∙ (C ∙ (D ∙ E)))) ∙ F) =₂
    (A ∙ (B ∙ (C ∙ (D ∙ (E ∙ F)))))
append-five A B C D E F =
  isoComp-cong (idIso A) (isoComp-cong (idIso B) (isoComp-cong (idIso C) (isoComp-assoc-at D E F))) ∙
  (isoComp-cong (idIso A) (isoComp-cong (idIso B) (isoComp-assoc-at C (D ∙ E) F)) ∙
  (isoComp-cong (idIso A) (isoComp-assoc-at B (C ∙ (D ∙ E)) F) ∙
    isoComp-assoc-at A (B ∙ (C ∙ (D ∙ E))) F))

append-square : {X Y : CAT} {a₀ a₁ a₂ a₃ b : MAP X Y}
  (U : a₂ =₁ a₃) (V : a₁ =₁ a₂) (W : b =₁ a₃)
  (P : a₁ =₁ b) (z : a₀ =₁ a₁) →
  (U ∙ V) =₂ (W ∙ P) → (U ∙ (V ∙ z)) =₂ (W ∙ (P ∙ z))
append-square U V W P z square = isoComp-assoc-at W P z ∙
  (isoComp-cong square (idIso z) ∙ (isoComp-assoc-at U V z) ⁻¹)

compose-evaluated-pasting : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ b : MAP X Y}
  (W : a₄ =₁ a₅) (O : a₃ =₁ a₄) (A : a₂ =₁ a₃)
  (P : a₁ =₁ a₂) (Z : a₀ =₁ a₁) (T : a₂ =₁ a₅)
  (R : b =₁ a₅) (S : a₁ =₁ b) (U : a₀ =₁ b) →
  (W ∙ (O ∙ A)) =₂ T → (T ∙ P) =₂ (R ∙ S) → (S ∙ Z) =₂ U →
  (W ∙ (O ∙ (A ∙ (P ∙ Z)))) =₂ (R ∙ U)
compose-evaluated-pasting W O A P Z T R S U output pasted source =
  isoComp-cong (idIso R) source ∙
  (isoComp-assoc-at R S Z ∙
  (isoComp-cong pasted (idIso Z) ∙
  ((isoComp-assoc-at T P Z) ⁻¹ ∙
  (isoComp-cong output (idIso (P ∙ Z)) ∙
  ((isoComp-assoc-at W (O ∙ A) (P ∙ Z)) ⁻¹ ∙
    isoComp-cong (idIso W) ((isoComp-assoc-at O A (P ∙ Z)) ⁻¹))))))

cancel-evaluation-route : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
  (d : a₃ =₁ a₄) (c : a₂ =₁ a₃) (b : a₁ =₁ a₂) (a : a₀ =₁ a₁) →
  ((d ∙ (c ∙ (b ∙ a))) ∙ (a ⁻¹ ∙ (b ⁻¹ ∙ c ⁻¹))) =₂ d
cancel-evaluation-route d c b a =
  isoComp-unitʳ-at d ∙
  (isoComp-cong (idIso d) (isoComp-inverseʳ-at c) ∙
  (isoComp-cong (idIso d) (isoComp-cong (idIso c) (cancel-inverse b (c ⁻¹))) ∙
  (isoComp-cong (idIso d) (isoComp-cong (idIso c)
    (isoComp-cong (idIso b) (cancel-inverse a (b ⁻¹ ∙ c ⁻¹)))) ∙
  (isoComp-cong (idIso d) (isoComp-cong (idIso c)
    (isoComp-assoc-at b a (a ⁻¹ ∙ (b ⁻¹ ∙ c ⁻¹)))) ∙
  (isoComp-cong (idIso d) (isoComp-assoc-at c (b ∙ a) (a ⁻¹ ∙ (b ⁻¹ ∙ c ⁻¹))) ∙
    isoComp-assoc-at d (c ∙ (b ∙ a)) (a ⁻¹ ∙ (b ⁻¹ ∙ c ⁻¹)))))))
cancel-evaluation-pairs : {X Y : CAT} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
  (a : a₁ =₁ a₂) (b : a₂ =₁ a₃) (c : a₃ =₁ a₄) (d : a₄ =₁ a₅)
  (u : a₀ =₁ a₁) →
  (((a ⁻¹ ∙ b ⁻¹) ∙ (c ⁻¹ ∙ d ⁻¹)) ∙
    (d ∙ (c ∙ (b ∙ (a ∙ u))))) =₂ u
cancel-evaluation-pairs a b c d u =
  cancel-left a u ∙
  (isoComp-cong (idIso (a ⁻¹)) (cancel-left b (a ∙ u)) ∙
  (isoComp-assoc-at (a ⁻¹) (b ⁻¹) (b ∙ (a ∙ u)) ∙
  (isoComp-cong (idIso (a ⁻¹ ∙ b ⁻¹))
    (cancel-left c (b ∙ (a ∙ u)) ∙
      (isoComp-cong (idIso (c ⁻¹)) (cancel-left d (c ∙ (b ∙ (a ∙ u)))) ∙
        isoComp-assoc-at (c ⁻¹) (d ⁻¹) (d ∙ (c ∙ (b ∙ (a ∙ u)))))) ∙
    isoComp-assoc-at (a ⁻¹ ∙ b ⁻¹) (c ⁻¹ ∙ d ⁻¹)
      (d ∙ (c ∙ (b ∙ (a ∙ u)))))))
changeEndpoints-compose : {X Y : CAT} {a₀ a₁ a₂ b₀ b₁ b₂ : MAP X Y}
  (p : a₀ =₁ a₁) (q : a₁ =₁ a₂) (r : b₀ =₁ b₁) (s : b₁ =₁ b₂)
  (γ : a₀ =₁ b₀) →
  (changeEndpoints (q ∙ p) (s ∙ r) γ) =₂
    (changeEndpoints q s (changeEndpoints p r γ))
changeEndpoints-compose p q r s γ =
  isoComp-cong (idIso s) ((isoComp-assoc-at r (γ ∙ p ⁻¹) (q ⁻¹)) ⁻¹) ∙
  (isoComp-cong (idIso s) (isoComp-cong (idIso r) ((isoComp-assoc-at γ (p ⁻¹) (q ⁻¹)) ⁻¹)) ∙
  (isoComp-assoc-at s r (γ ∙ (p ⁻¹ ∙ q ⁻¹)) ∙
    isoComp-cong (idIso (s ∙ r)) (isoComp-cong (idIso γ) (inverse-composite q p))))

close-evaluation-square : {X Y : CAT} {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : MAP X Y}
  (A : a₀ =₁ a₁) (B : b₀ =₁ b₁)
  (L : a₁ =₁ a₂) (R : b₁ =₁ b₂)
  (a : a₂ =₁ a₃) (b : b₂ =₁ b₃)
  (γ : a₀ =₁ b₀) (δ : a₃ =₁ b₃) →
  (δ ∙ (a ∙ (L ∙ A))) =₂ ((b ∙ (R ∙ B)) ∙ γ) →
  ((b ⁻¹ ∙ (δ ∙ a)) ∙ L) =₂ (R ∙ changeEndpoints A B γ)
close-evaluation-square A B L R a b γ δ square =
  encoded-restriction-square A B L R target γ image
  where
  target = b ⁻¹ ∙ (δ ∙ a)
  compact : (target ∙ (L ∙ A)) =₂ ((R ∙ B) ∙ γ)
  compact = cancel-left b ((R ∙ B) ∙ γ) ∙
    (isoComp-cong (idIso (b ⁻¹))
      (isoComp-assoc-at b (R ∙ B) γ ∙ square) ∙
    (isoComp-cong (idIso (b ⁻¹)) (isoComp-assoc-at δ a (L ∙ A)) ∙
      isoComp-assoc-at (b ⁻¹) (δ ∙ a) (L ∙ A)))
  image : γ =₂ ((R ∙ B) ⁻¹ ∙ (target ∙ (L ∙ A)))
  image = isoComp-cong (idIso ((R ∙ B) ⁻¹)) (compact ⁻¹) ∙
    (cancel-left (R ∙ B) γ) ⁻¹
```
