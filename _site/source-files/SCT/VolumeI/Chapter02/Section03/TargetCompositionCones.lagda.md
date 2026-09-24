# Composition acting on cones of arrows

For a family of arrows from `x` to `y`, composition sends an arrow ending
at `x` to an arrow ending at `y`. It respects whole cone comparisons and
restriction of the parameter category, including the endpoint matching.

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

module SCT.VolumeI.Chapter02.Section03.TargetCompositionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.ExpressionParameterChanges 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.ExpressionRestriction 𝒯 M ℱ I using (restrict-expression-compose)
open import SCT.VolumeI.Chapter02.Section02.CompositionSubstitution 𝒯 M ℱ P I E S using (restrict-composition)

module Action {B C : CAT} {x y : MAP B C} (f : MorphismExpression x y) where
  input : {Γ : CAT} (t : Cone (ev₁ {C}) x Γ) →
    MorphismExpression (ev₀ ∘ Cone.left t) (x ∘ Cone.right t)
  input t = record { arrow = Cone.left t
    ; source-frame = idIso (ev₀ ∘ Cone.left t) ; target-frame = Cone.match t }

  composite : {Γ : CAT} (t : Cone (ev₁ {C}) x Γ) →
    MorphismExpression (ev₀ ∘ Cone.left t) (y ∘ Cone.right t)
  composite t = compose-expression (input t) (restrict-expression f (Cone.right t))

  act : {Γ : CAT} → Cone (ev₁ {C}) x Γ → Cone (ev₁ {C}) y Γ
  act t = record { left = MorphismExpression.arrow (composite t)
    ; right = Cone.right t ; match = MorphismExpression.target-frame (composite t) }

  module Compared {Γ : CAT} {t u : Cone (ev₁ {C}) x Γ} (Φ : ConeIso t u) where
    private
      L = ConeIso.leftIso Φ
      R = ConeIso.rightIso Φ
      source-change = ev₀ ◁ L
      middle-change = x ◁ R
      target-change = y ◁ R

      input-comparison : ExpressionIso
        (retarget-expression (input t) source-change middle-change) (input u)
      input-comparison = record { comparison = L
        ; source-compatible = (isoComp-unitʳ-at source-change) ⁻¹ ∙ isoComp-unitˡ-at source-change
        ; target-compatible = ConeIso.compatible Φ }

      value : ExpressionIso (retarget-expression (composite t) source-change target-change) (composite u)
      value = composition-square (input t) (restrict-expression f (Cone.right t))
        (input u) (restrict-expression f (Cone.right u)) source-change middle-change target-change
        input-comparison (restrict-parameter f R)

    comparison : ConeIso (act t) (act u)
    comparison = record { leftIso = ExpressionIso.comparison value ; rightIso = R
      ; compatible = ExpressionIso.target-compatible value }

  module Restriction {Γ Δ : CAT} (t : Cone (ev₁ {C}) x Γ) (r : MAP Δ Γ) where
    private
      p = Cone.left t
      q = Cone.right t
      source-assoc = comp-assoc r p ev₀
      b = comp-assoc r q x
      c′ = comp-assoc r q y
      changed = conePre r t

      input-comparison : ExpressionIso
        (retarget-expression (restrict-expression (input t) r) source-assoc b) (input changed)
      input-comparison = record { comparison = idIso (p ∘ r)
        ; source-compatible =
            (isoComp-inverseʳ-at source-assoc ∙ isoComp-cong (idIso source-assoc)
              (isoComp-unitˡ-at (source-assoc ⁻¹) ∙ isoComp-cong (preWhisker-idIso (ev₀ ∘ p) r) (idIso (source-assoc ⁻¹)))) ⁻¹ ∙
            isoComp-unitˡ-at (idIso (ev₀ ∘ (p ∘ r))) ∙
            isoComp-cong (idIso (idIso (ev₀ ∘ (p ∘ r)))) (postWhisker-idIso ev₀ (p ∘ r))
        ; target-compatible = isoComp-unitʳ-at (Cone.match changed) ∙
            isoComp-cong (idIso (Cone.match changed)) (postWhisker-idIso ev₁ (p ∘ r)) }

      output-comparison : ExpressionIso
        (retarget-expression (restrict-expression (composite t) r) source-assoc c′) (composite changed)
      output-comparison = expressionIso-compose
        (composition-square (restrict-expression (input t) r)
          (restrict-expression (restrict-expression f q) r)
          (input changed) (restrict-expression f (q ∘ r)) source-assoc b c′
          input-comparison (restrict-expression-compose f q r))
        (retarget-expressionIso
          (expressionIso-inverse (restrict-composition (input t) (restrict-expression f q) r)) source-assoc c′)

    comparison : ConeIso (conePre r (act t)) (act (conePre r t))
    comparison = record { leftIso = ExpressionIso.comparison output-comparison
      ; rightIso = idIso (q ∘ r)
      ; compatible =
          (isoComp-unitˡ-at (Cone.match (conePre r (act t))) ∙
            isoComp-cong (postWhisker-idIso y (q ∘ r)) (idIso (Cone.match (conePre r (act t))))) ⁻¹ ∙
          ExpressionIso.target-compatible output-comparison }
```
