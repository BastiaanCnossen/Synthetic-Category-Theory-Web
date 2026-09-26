# Composition acting on source cones

For a family of arrows from `y` to `x`, composition sends an arrow starting
at `x` to an arrow starting at `y`. The source matching is retained under
cone comparisons and parameter restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section03.CompositionCalculus.SourceCompositionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionParameterChanges 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expression-compose)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (restrict-composition)

module Action {B C : CAT} {x y : MAP B C} (f : MorphismExpression y x) where
  input : {Γ : CAT} (t : Cone (ev₀ {C}) x Γ) →
    MorphismExpression (x ∘ Cone.right t) (ev₁ ∘ Cone.left t)
  input t = record { arrow = Cone.left t
    ; target-frame = idIso (ev₁ ∘ Cone.left t) ; source-frame = Cone.match t }

  composite : {Γ : CAT} (t : Cone (ev₀ {C}) x Γ) →
    MorphismExpression (y ∘ Cone.right t) (ev₁ ∘ Cone.left t)
  composite t = compose-expression (restrict-expression f (Cone.right t)) (input t)

  act : {Γ : CAT} → Cone (ev₀ {C}) x Γ → Cone (ev₀ {C}) y Γ
  act t = record { left = MorphismExpression.arrow (composite t)
    ; right = Cone.right t ; match = MorphismExpression.source-frame (composite t) }

  module Compared {Γ : CAT} {t u : Cone (ev₀ {C}) x Γ} (Φ : ConeIso t u) where
    private
      L = ConeIso.leftIso Φ
      R = ConeIso.rightIso Φ
      source-change = ev₁ ◁ L
      middle-change = x ◁ R
      target-change = y ◁ R

      input-comparison : ExpressionIso
        (retarget-expression (input t) middle-change source-change) (input u)
      input-comparison = record { comparison = L
        ; target-compatible = (isoComp-unitʳ-at source-change) ⁻¹ ∙ isoComp-unitˡ-at source-change
        ; source-compatible = ConeIso.compatible Φ }

      value : ExpressionIso (retarget-expression (composite t) target-change source-change) (composite u)
      value = composition-square (restrict-expression f (Cone.right t)) (input t)
        (restrict-expression f (Cone.right u)) (input u) target-change middle-change source-change
        (restrict-parameter f R) input-comparison

    comparison : ConeIso (act t) (act u)
    comparison = record { leftIso = ExpressionIso.comparison value ; rightIso = R
      ; compatible = ExpressionIso.source-compatible value }

  module Restriction {Γ Δ : CAT} (t : Cone (ev₀ {C}) x Γ) (r : MAP Δ Γ) where
    private
      p = Cone.left t
      q = Cone.right t
      source-assoc = comp-assoc r p ev₁
      b = comp-assoc r q x
      c′ = comp-assoc r q y
      changed = conePre r t

      input-comparison : ExpressionIso
        (retarget-expression (restrict-expression (input t) r) b source-assoc) (input changed)
      input-comparison = record { comparison = idIso (p ∘ r)
        ; target-compatible =
            (isoComp-inverseʳ-at source-assoc ∙ isoComp-cong (idIso source-assoc)
              (isoComp-unitˡ-at (source-assoc ⁻¹) ∙ isoComp-cong (preWhisker-idIso (ev₁ ∘ p) r) (idIso (source-assoc ⁻¹)))) ⁻¹ ∙
            isoComp-unitˡ-at (idIso (ev₁ ∘ (p ∘ r))) ∙
            isoComp-cong (idIso (idIso (ev₁ ∘ (p ∘ r)))) (postWhisker-idIso ev₁ (p ∘ r))
        ; source-compatible = isoComp-unitʳ-at (Cone.match changed) ∙
            isoComp-cong (idIso (Cone.match changed)) (postWhisker-idIso ev₀ (p ∘ r)) }

      output-comparison : ExpressionIso
        (retarget-expression (restrict-expression (composite t) r) c′ source-assoc) (composite changed)
      output-comparison = expressionIso-compose
        (composition-square (restrict-expression (restrict-expression f q) r)
          (restrict-expression (input t) r)
          (restrict-expression f (q ∘ r)) (input changed) c′ b source-assoc
          (restrict-expression-compose f q r) input-comparison)
        (retarget-expressionIso
          (expressionIso-inverse (restrict-composition (restrict-expression f q) (input t) r)) c′ source-assoc)

    comparison : ConeIso (conePre r (act t)) (act (conePre r t))
    comparison = record { leftIso = ExpressionIso.comparison output-comparison
      ; rightIso = idIso (q ∘ r)
      ; compatible =
          (isoComp-unitˡ-at (Cone.match (conePre r (act t))) ∙
            isoComp-cong (postWhisker-idIso y (q ∘ r)) (idIso (Cone.match (conePre r (act t))))) ⁻¹ ∙
          ExpressionIso.source-compatible output-comparison }
```
