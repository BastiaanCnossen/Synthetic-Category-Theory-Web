# Restriction of families with constant source

Normalize only the constant source after substitution. Successive
restrictions agree with restriction along the composite, retaining the
associator at the varying target. This applies in particular to the
universal arrows of coslices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expression-compose; restrict-expressionIso; restrict-expression-parameter)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget-outer; retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (const-pre-compose; const-pre-natural; constant-image; constant-image-pre)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)

restrict : {Γ Δ C : CAT} {x : Obj-abs C} {q : MAP Γ C} →
  MorphismExpression (const x) q → (r : MAP Δ Γ) → MorphismExpression (const x) (q ∘ r)
restrict {x = x} {q} f r = retarget-expression (restrict-expression f r) (const-pre x r) (idIso (q ∘ r))

module Successive {Γ Δ Θ C : CAT} {x : Obj-abs C} {q : MAP Γ C}
  (f : MorphismExpression (const x) q) (r : MAP Δ Γ) (s : MAP Θ Δ) where
  private
    raw = restrict-expression (restrict-expression f r) s
    A₀ = comp-assoc s r (const x)
    B₀ = comp-assoc s r q
    p = const-pre x s ∙ (const-pre x r ▷ s)
    t = B₀ ∙ (idIso (q ∘ r) ▷ s)
    p′ = const-pre x (r ∘ s) ∙ A₀
    t′ = idIso (q ∘ (r ∘ s)) ∙ B₀

    abstract
      source-frame : p′ =₂ p
      source-frame = cancel-inverse-tail p A₀ ∙
        isoComp-cong ((isoComp-assoc-at (const-pre x s) (const-pre x r ▷ s) (A₀ ⁻¹)) ⁻¹ ∙
          (const-pre-compose x s r) ⁻¹) (idIso A₀)
      target-frame : t =₂ t′
      target-frame = (isoComp-unitˡ-at B₀) ⁻¹ ∙
        (isoComp-unitʳ-at B₀ ∙ isoComp-cong (idIso B₀) (preWhisker-idIso (q ∘ r) s))

  abstract
    comparison : ExpressionIso
      (retarget-expression (restrict-expression (restrict f r) s) (const-pre x s) B₀)
      (restrict f (r ∘ s))
    comparison = expressionIso-compose
      (retarget-expressionIso (restrict-expression-compose f r s) (const-pre x (r ∘ s)) (idIso (q ∘ (r ∘ s))))
      (expressionIso-compose (expressionIso-inverse
        (retarget-assoc raw A₀ B₀ (const-pre x (r ∘ s)) (idIso (q ∘ (r ∘ s)))))
      (expressionIso-compose (retarget-cong raw (source-frame ⁻¹) target-frame)
        (restrict-retarget-outer (restrict-expression f r) (const-pre x r) (idIso (q ∘ r)) s
          (const-pre x s) B₀)))

module Parameter {Γ Δ C : CAT} {x : Obj-abs C} {q : MAP Γ C}
  (f : MorphismExpression (const x) q) {r s : MAP Δ Γ} (δ : r =₁ s) where
  private
    raw = restrict-expression f r
    a₀ = const-pre x r
    a₁ = const-pre x s
    p = const x ◁ δ
    t = q ◁ δ
    abstract
      source-frame : (idIso (const x) ∙ a₀) =₂ (a₁ ∙ p)
      source-frame = (const-pre-natural x δ) ⁻¹ ∙ isoComp-unitˡ-at a₀
      target-frame : (t ∙ idIso (q ∘ r)) =₂ (idIso (q ∘ s) ∙ t)
      target-frame = (isoComp-unitˡ-at t) ⁻¹ ∙ isoComp-unitʳ-at t

  abstract
    comparison : ExpressionIso
      (retarget-expression (restrict f r) (idIso (const x)) t) (restrict f s)
    comparison = expressionIso-compose
      (retarget-expressionIso (restrict-expression-parameter f δ) a₁ (idIso (q ∘ s)))
      (expressionIso-compose (expressionIso-inverse (retarget-assoc raw p t a₁ (idIso (q ∘ s))))
      (expressionIso-compose (retarget-cong raw source-frame target-frame)
        (retarget-assoc raw a₀ (idIso (q ∘ r)) (idIso (const x)) t)))

module Fixed {B C : CAT} {x : Obj-abs C} {q : MAP B C}
  (f : MorphismExpression (const x) q) (u : Obj-abs B) where
  family : (Γ : CAT) → MorphismExpression (const {P = Γ} x) (const (q ∘ u))
  family Γ = retarget-expression (restrict f (const u)) (idIso (const x)) (constant-image Γ q u)

  module Restrict {Γ Δ : CAT} (h : MAP Δ Γ) where
    private
      old = restrict f (const {P = Γ} u)
      raw = restrict-expression old h
      mid = restrict f ((const {P = Γ} u) ∘ h)
      p = const-pre x h
      a₀ = comp-assoc h (const u) q
      b₀ = q ◁ const-pre u h
      γ₀ = constant-image Γ q u
      γ₁ = constant-image Δ q u
      source-id = idIso (const {P = Δ} x)
      module First = Successive f (const {P = Γ} u) h using (comparison)
      module Second = Parameter f (const-pre u h) using (comparison)

      abstract
        source-frame : (p ∙ (idIso (const {P = Γ} x) ▷ h)) =₂ (source-id ∙ p)
        source-frame = (isoComp-unitˡ-at p) ⁻¹ ∙
          (isoComp-unitʳ-at p ∙ isoComp-cong (idIso p) (preWhisker-idIso (const {P = Γ} x) h))
        target-frame : (const-pre (q ∘ u) h ∙ (γ₀ ▷ h)) =₂ ((γ₁ ∙ b₀) ∙ a₀)
        target-frame = (isoComp-assoc-at γ₁ b₀ a₀) ⁻¹ ∙ constant-image-pre h q u
        finish : ExpressionIso (retarget-expression mid source-id (γ₁ ∙ b₀)) (family Δ)
        finish = expressionIso-compose (retarget-expressionIso Second.comparison source-id γ₁)
          (expressionIso-compose (expressionIso-inverse (retarget-assoc mid source-id b₀ source-id γ₁))
            (retarget-cong mid ((isoComp-unitˡ-at source-id) ⁻¹) (idIso (γ₁ ∙ b₀))))

    abstract
      comparison : ExpressionIso
        (retarget-expression (restrict-expression (family Γ) h) (const-pre x h) (const-pre (q ∘ u) h))
        (family Δ)
      comparison = expressionIso-compose finish
        (expressionIso-compose (retarget-expressionIso First.comparison source-id (γ₁ ∙ b₀))
        (expressionIso-compose (expressionIso-inverse (retarget-assoc raw p a₀ source-id (γ₁ ∙ b₀)))
        (expressionIso-compose (retarget-cong raw source-frame target-frame)
          (restrict-retarget-outer old (idIso (const x)) γ₀ h p (const-pre (q ∘ u) h)))))
```
