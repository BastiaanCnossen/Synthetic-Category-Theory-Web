# Restriction with prescribed endpoint frames

The two comparison lemmas combine restriction with postcomposition or
with another restriction. Their endpoint equations are explicit inputs:
these identify the chosen frames, while the arrow comparison is proved
by the restriction calculus.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget-outer; retarget-cong; retarget-assoc; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expression-compose)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I
  using (restrict-post)

abstract
  restrict-post-retarget : {Γ Δ C D : CAT} (F : MAP C D) {f g : MAP Γ C}
    (t : MorphismExpression f g) (x : MAP Δ Γ) {u v : MAP Γ D}
    (p : (F ∘ f) =₁ u) (q : (F ∘ g) =₁ v) {w z : MAP Δ D}
    (a : (u ∘ x) =₁ w) (b : (v ∘ x) =₁ z)
    (p′ : (F ∘ (f ∘ x)) =₁ w) (q′ : (F ∘ (g ∘ x)) =₁ z) →
    (a ∙ (p ▷ x)) =₂ (p′ ∙ comp-assoc x f F) →
    (b ∙ (q ▷ x)) =₂ (q′ ∙ comp-assoc x g F) →
    ExpressionIso (retarget-expression (restrict-expression (retarget-expression (post-expression F t) p q) x) a b)
      (retarget-expression (post-expression F (restrict-expression t x)) p′ q′)
  restrict-post-retarget F t x p q a b p′ q′ source target = expressionIso-compose
    (retarget-expressionIso (restrict-post F t x) p′ q′)
    (expressionIso-compose
      (expressionIso-inverse (retarget-assoc (restrict-expression (post-expression F t) x) _ _ p′ q′))
      (expressionIso-compose (retarget-cong _ source target)
        (restrict-retarget-outer (post-expression F t) p q x a b)))

  restrict-restriction-retarget : {Γ Δ Θ C : CAT} {f g : MAP Γ C}
    (t : MorphismExpression f g) (r : MAP Δ Γ) (x : MAP Θ Δ) {u v : MAP Δ C}
    (p : (f ∘ r) =₁ u) (q : (g ∘ r) =₁ v) {w z : MAP Θ C}
    (a : (u ∘ x) =₁ w) (b : (v ∘ x) =₁ z)
    (p′ : (f ∘ (r ∘ x)) =₁ w) (q′ : (g ∘ (r ∘ x)) =₁ z) →
    (a ∙ (p ▷ x)) =₂ (p′ ∙ comp-assoc x r f) →
    (b ∙ (q ▷ x)) =₂ (q′ ∙ comp-assoc x r g) →
    ExpressionIso (retarget-expression (restrict-expression (retarget-expression (restrict-expression t r) p q) x) a b)
      (retarget-expression (restrict-expression t (r ∘ x)) p′ q′)
  restrict-restriction-retarget t r x p q a b p′ q′ source target = expressionIso-compose
    (retarget-expressionIso (restrict-expression-compose t r x) p′ q′)
    (expressionIso-compose
      (expressionIso-inverse (retarget-assoc (restrict-expression (restrict-expression t r) x) _ _ p′ q′))
      (expressionIso-compose (retarget-cong _ source target)
        (restrict-retarget-outer (restrict-expression t r) p q x a b)))

  restrict-post-frames : {Γ Δ C D : CAT} (F : MAP C D) {x y : MAP Γ C}
    (f : MorphismExpression x y) (h : MAP Δ Γ) {x′ y′ : MAP Δ C}
    (p : (x ∘ h) =₁ x′) (q : (y ∘ h) =₁ y′) →
    ExpressionIso (retarget-expression (restrict-expression (post-expression F f) h)
      ((F ◁ p) ∙ comp-assoc h x F) ((F ◁ q) ∙ comp-assoc h y F))
      (post-expression F (retarget-expression (restrict-expression f h) p q))
  restrict-post-frames F {x} {y} f h p q = expressionIso-compose
    (expressionIso-inverse (post-retarget F (restrict-expression f h) p q))
    (expressionIso-compose (retarget-expressionIso (restrict-post F f h) (F ◁ p) (F ◁ q))
      (expressionIso-inverse (retarget-assoc (restrict-expression (post-expression F f) h)
        (comp-assoc h x F) (comp-assoc h y F) (F ◁ p) (F ◁ q))))
```
