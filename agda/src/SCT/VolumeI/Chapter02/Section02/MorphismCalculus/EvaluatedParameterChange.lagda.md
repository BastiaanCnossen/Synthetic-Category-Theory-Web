# Evaluating a change of parameter

A paired parameter comparison passes through an identified evaluator.
Its endpoint frames retain both the separation comparison and the
chosen comparison for the final coordinate functor.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I using (restrict-post-frames)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting 𝒯 M ℱ P I E using (post-composite)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting

private
  paste : {Γ C : CAT} {x y u v w z : MAP Γ C}
    (α : MorphismExpression x y) {β : MorphismExpression u v} {γ : MorphismExpression w z}
    (p : x =₁ u) (q : y =₁ v) (r : u =₁ w) (s : v =₁ z) →
    ExpressionIso (retarget-expression α p q) β →
    ExpressionIso (retarget-expression β r s) γ →
    ExpressionIso (retarget-expression α (r ∙ p) (s ∙ q)) γ
  paste α p q r s ξ ζ = expressionIso-compose ζ
    (expressionIso-compose (retarget-expressionIso ξ r s)
      (expressionIso-inverse (retarget-assoc α p q r s)))

module At {A B C K : CAT} (σ : MAP A B) (W : MAP A C)
  (d : MAP B K) (e : MAP C K) (β : (d ∘ σ) =₁ (e ∘ W))
  {v₀ v₁ : MAP B B} {z₀ z₁ : MAP A A} {w₀ w₁ : MAP A C}
  (γY : MorphismExpression v₀ v₁) (γX : MorphismExpression z₀ z₁) (γZ : MorphismExpression w₀ w₁)
  (ν₀ : (v₀ ∘ σ) =₁ (σ ∘ z₀)) (ν₁ : (v₁ ∘ σ) =₁ (σ ∘ z₁))
  (χ₀ : (W ∘ z₀) =₁ w₀) (χ₁ : (W ∘ z₁) =₁ w₁)
  (parameter : ExpressionIso (retarget-expression (restrict-expression γY σ) ν₀ ν₁) (post-expression σ γX))
  (coordinate : ExpressionIso (retarget-expression (post-expression W γX) χ₀ χ₁) γZ) where
  original = restrict-expression (post-expression d γY) σ
  module Endpoint (v : MAP B B) (z : MAP A A) {w : MAP A C}
    (ν : (v ∘ σ) =₁ (σ ∘ z)) (χ : (W ∘ z) =₁ w) where
    p = (d ◁ ν) ∙ comp-assoc σ v d
    q = (β ▷ z) ∙ (comp-assoc z σ d) ⁻¹
    r = comp-assoc z W e
    s = e ◁ χ
    combined = ((s ∙ r) ∙ q) ∙ p
    changed = (comp-assoc z σ d) ⁻¹ ∙ p
    n = s ∙ (r ∙ (β ▷ z))
    Ξ = n ∙ changed
    abstract
      normalization : combined =₂ Ξ
      normalization = isoComp-cong (isoComp-assoc-at s r (β ▷ z)) (idIso changed) ∙
        isoComp-assoc-at ((s ∙ r) ∙ (β ▷ z)) ((comp-assoc z σ d) ⁻¹) p ∙
        isoComp-cong ((isoComp-assoc-at (s ∙ r) (β ▷ z) ((comp-assoc z σ d) ⁻¹)) ⁻¹) (idIso p)
  module Source = Endpoint v₀ z₀ ν₀ χ₀
  module Target = Endpoint v₁ z₁ ν₁ χ₁
  module Identified = Pasting.At 𝒯 M ℱ P I E σ d (e ∘ W) β γX

  abstract
    restricted : ExpressionIso (retarget-expression original Source.p Target.p)
      (post-expression d (post-expression σ γX))
    restricted = expressionIso-compose (post-expressionIso d parameter)
      (restrict-post-frames d γY σ ν₀ ν₁)

    evaluated : ExpressionIso (retarget-expression (post-expression (e ∘ W) γX)
      (Source.s ∙ Source.r) (Target.s ∙ Target.r)) (post-expression e γZ)
    evaluated = paste (post-expression (e ∘ W) γX) Source.r Target.r Source.s Target.s
      (post-composite W e γX)
      (expressionIso-compose (post-expressionIso e coordinate)
        (expressionIso-inverse (post-retarget e (post-expression W γX) χ₀ χ₁)))

    combined : ExpressionIso (retarget-expression original Source.combined Target.combined)
      (post-expression e γZ)
    combined = paste original Source.p Target.p
      ((Source.s ∙ Source.r) ∙ Source.q) ((Target.s ∙ Target.r) ∙ Target.q) restricted
      (paste (post-expression d (post-expression σ γX)) Source.q Target.q
        (Source.s ∙ Source.r) (Target.s ∙ Target.r) Identified.comparison evaluated)

    value : ExpressionIso (retarget-expression original Source.Ξ Target.Ξ) (post-expression e γZ)
    value = expressionIso-compose combined
      (retarget-cong original (Source.normalization ⁻¹) (Target.normalization ⁻¹))
```
