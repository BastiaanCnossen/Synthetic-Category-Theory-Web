# Lifting comparisons of diagrams with fixed endpoints

Uncurrying reflects a diagram comparison together with both endpoint
equations. The image witness of the lift and naturality of evaluation
ensure that no boundary data are discarded.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.DiagramComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ using (module Evaluation)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ

undo-frame : {X C : CAT} {h k f : MAP X C} (q : h =₁ k) (b : h =₁ f) →
  ((b ∙ q ⁻¹) ∙ q) =₂ b
undo-frame q b = isoComp-unitʳ-at b ∙
  (isoComp-cong (idIso b) (isoComp-inverseˡ-at q) ∙ isoComp-assoc-at b (q ⁻¹) q)

frame-square : {X C : CAT} {h k H K f : MAP X C}
  (q : h =₁ H) (r : k =₁ K) (b : h =₁ f) (d : k =₁ f)
  (δ : h =₁ k) (D : H =₁ K) →
  (r ∙ δ) =₂ (D ∙ q) → ((d ∙ r ⁻¹) ∙ D) =₂ (b ∙ q ⁻¹) →
  (d ∙ δ) =₂ b
frame-square q r b d δ D natural compatible = undo-frame q b ∙
  (isoComp-unitˡ-at ((b ∙ q ⁻¹) ∙ q) ∙
  (paste-squares q r (b ∙ q ⁻¹) (d ∙ r ⁻¹) δ D (idIso _)
    natural ((isoComp-unitˡ-at (b ∙ q ⁻¹)) ⁻¹ ∙ compatible) ∙
    isoComp-cong ((undo-frame r d) ⁻¹) (idIso δ)))

module Lift {Γ C : CAT} {f g : MAP Γ C} (α β : MorphismExpression f g)
  (θ : (funUncurry (MorphismExpression.arrow α)) =₁ (funUncurry (MorphismExpression.arrow β))) where
  module A = MorphismExpression α
  module B = MorphismExpression β
  δ = funIsoReflect A.arrow B.arrow θ

  endpoint : (x : Obj-abs [1]) {z : MAP Γ C}
    (p : (evaluate x ∘ A.arrow) =₁ z) (q : (evaluate x ∘ B.arrow) =₁ z) →
    ((q ∙ (evaluate-uncurry x B.arrow) ⁻¹) ∙ (θ ▷ insert x)) =₂
      (p ∙ (evaluate-uncurry x A.arrow) ⁻¹) → (q ∙ (evaluate x ◁ δ)) =₂ p
  endpoint x p q compatible = frame-square
    (evaluate-uncurry x A.arrow) (evaluate-uncurry x B.arrow) p q (evaluate x ◁ δ) (θ ▷ insert x)
    (isoComp-cong (preWhisker (insert x) ◁ funIsoReflect-β A.arrow B.arrow θ)
      (idIso (evaluate-uncurry x A.arrow)) ∙ Evaluation.natural x δ) compatible

  comparison :
    ((B.source-frame ∙ (evaluate-uncurry zero B.arrow) ⁻¹) ∙ (θ ▷ insert zero)) =₂
      (A.source-frame ∙ (evaluate-uncurry zero A.arrow) ⁻¹) →
    ((B.target-frame ∙ (evaluate-uncurry one B.arrow) ⁻¹) ∙ (θ ▷ insert one)) =₂
      (A.target-frame ∙ (evaluate-uncurry one A.arrow) ⁻¹) → ExpressionIso α β
  comparison source target = record
    { comparison = δ
    ; source-compatible = endpoint zero A.source-frame B.source-frame source
    ; target-compatible = endpoint one A.target-frame B.target-frame target }
```
