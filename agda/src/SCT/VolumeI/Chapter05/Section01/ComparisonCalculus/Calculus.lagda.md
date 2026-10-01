# Calculus of identification chains

The following calculations use the finite vertical and whiskering laws of a theory copy. Forward-reading composition and middle-square replacement retain the parenthesization of each chain.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus {l : Level} (T : Theory l l l) where
open View T
open Specialization vocabulary terminal products productLaws composition public
open Specialization.Units vocabulary terminal products productLaws composition vertical public
open Specialization.Whiskering vocabulary terminal products productLaws composition whiskering public
open Parameterized vocabulary terminal products productLaws composition vertical public
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering public

-- A forward-reading chain of actual synthetic identifications.
infixl 1 _then_
_then_ : {C D : CAT} {f g h : MAP C D} → f =₁ g → g =₁ h → f =₁ h
p then q = q ∙ p

-- Substitute a commuting middle square, retaining the exact outer brackets.
middle-square : {C D : CAT} {f₀ f₁ f₂ f₃ f₄ f₅ t : MAP C D}
  (a : f₄ =₁ f₅) (b : f₃ =₁ f₄) (c : f₂ =₁ f₃)
  (d : f₁ =₁ f₂) (z : f₀ =₁ f₁) (e : t =₁ f₃) (v : f₁ =₁ t)
  → (c ∙ d) =₂ (e ∙ v)
  → ((a ∙ (b ∙ c)) ∙ (d ∙ z)) =₂ (a ∙ ((b ∙ e) ∙ (v ∙ z)))
middle-square a b c d z e v square =
  isoComp-assoc-at a (b ∙ c) (d ∙ z) then
  isoComp-cong (idIso _) (isoComp-assoc-at b c (d ∙ z)) then
  isoComp-cong (idIso _) (isoComp-cong (idIso _)
    ((isoComp-assoc-at c d z) ⁻¹ then isoComp-cong square (idIso _) then
      isoComp-assoc-at e v z)) then
  isoComp-cong (idIso _) ((isoComp-assoc-at b e (v ∙ z)) ⁻¹)

five-middle : {C D : CAT} {f₀ f₁ f₂ f₃ f₄ f₅ t : MAP C D}
  (a : f₄ =₁ f₅) (b : f₃ =₁ f₄) (c : f₂ =₁ f₃)
  (d : f₁ =₁ f₂) (e : f₀ =₁ f₁) (u : t =₁ f₄) (v : f₂ =₁ t)
  → (b ∙ c) =₂ (u ∙ v)
  → ((a ∙ b) ∙ ((c ∙ d) ∙ e)) =₂ (a ∙ (u ∙ (v ∙ (d ∙ e))))
five-middle a b c d e u v square =
  isoComp-assoc-at a b ((c ∙ d) ∙ e) then
  isoComp-cong (idIso _) (isoComp-cong (idIso _) (isoComp-assoc-at c d e)) then
  isoComp-cong (idIso _) ((isoComp-assoc-at b c (d ∙ e)) ⁻¹ then
    isoComp-cong square (idIso _) then isoComp-assoc-at u v (d ∙ e))

three-prefix : {C D : CAT} {f₀ f₁ f₂ f₃ f₄ : MAP C D}
  (a : f₃ =₁ f₄) (b : f₂ =₁ f₃) (c : f₁ =₁ f₂) (d : f₀ =₁ f₁)
  → (a ∙ (b ∙ (c ∙ d))) =₂ ((a ∙ (b ∙ c)) ∙ d)
three-prefix a b c d =
  isoComp-cong (idIso _) ((isoComp-assoc-at b c d) ⁻¹) then
  (isoComp-assoc-at a (b ∙ c) d) ⁻¹

decorate-square : {C D : CAT} {f₀ f₁ f₂ f₃ f₄ s t : MAP C D}
  (q : f₃ =₁ f₄) (a : f₂ =₁ f₃) (b : f₁ =₁ f₂) (x : f₀ =₁ f₁)
  (v : s =₁ f₃) (c : f₀ =₁ s) (v' : t =₁ f₄) (r : s =₁ t)
  → (a ∙ (b ∙ x)) =₂ (v ∙ c) → (q ∙ v) =₂ (v' ∙ r)
  → ((q ∙ (a ∙ b)) ∙ x) =₂ (v' ∙ (r ∙ c))
decorate-square q a b x v c v' r square naturality =
  isoComp-assoc-at q (a ∙ b) x then
  isoComp-cong (idIso _) (isoComp-assoc-at a b x then square) then
  (isoComp-assoc-at q v c) ⁻¹ then
  isoComp-cong naturality (idIso _) then isoComp-assoc-at v' r c

hcomp-idOuter : {C D E : CAT} {f g : MAP C D} (u : MAP D E) (alpha : f =₁ g)
  → (idIso u ⋆ alpha) =₂ (u ◁ alpha)
hcomp-idOuter {g = g} u alpha =
  isoComp-cong (preWhisker-idIso u g) (idIso _) then isoComp-unitˡ-at _

hcomp-idInner : {B C D : CAT} {f g : MAP C D} (alpha : f =₁ g) (k : MAP B C)
  → (alpha ⋆ idIso k) =₂ (alpha ▷ k)
hcomp-idInner {f = f} alpha k =
  isoComp-cong (idIso _) (postWhisker-idIso f k) then isoComp-unitʳ-at _
```
