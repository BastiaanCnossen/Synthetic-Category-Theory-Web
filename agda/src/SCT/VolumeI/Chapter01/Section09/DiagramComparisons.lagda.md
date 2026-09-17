# Lifting comparisons of diagrams with fixed endpoints

Uncurrying reflects a diagram comparison together with both endpoint
equations. The image witness of the lift and naturality of evaluation
ensure that no boundary data are discarded.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.DiagramComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section09.EndpointNaturality 𝒯 M ℱ using (module Evaluation)
open import SCT.VolumeI.Chapter01.Section06.IsomorphismLifting 𝒯 M ℱ

undo-frame : {X C : CAT} {h k f : MAP X C} (q : =₁ h k) (b : =₁ h f) →
  =₂ ((b ∙ invIso q) ∙ q) b
undo-frame q b = isoComp-unitʳ-at b ∙
  (isoComp-cong (idIso b) (isoComp-inverseˡ-at q) ∙ isoComp-assoc-at b (invIso q) q)

frame-square : {X C : CAT} {h k H K f : MAP X C}
  (q : =₁ h H) (r : =₁ k K) (b : =₁ h f) (d : =₁ k f)
  (δ : =₁ h k) (D : =₁ H K) →
  =₂ (r ∙ δ) (D ∙ q) → =₂ ((d ∙ invIso r) ∙ D) (b ∙ invIso q) →
  =₂ (d ∙ δ) b
frame-square q r b d δ D natural compatible = undo-frame q b ∙
  (isoComp-unitˡ-at ((b ∙ invIso q) ∙ q) ∙
  (paste-squares q r (b ∙ invIso q) (d ∙ invIso r) δ D (idIso _)
    natural (invIso (isoComp-unitˡ-at (b ∙ invIso q)) ∙ compatible) ∙
    isoComp-cong (invIso (undo-frame r d)) (idIso δ)))

module Lift {Γ C : CAT} {f g : MAP Γ C} (α β : MorphismExpression f g)
  (θ : =₁ (funUncurry (MorphismExpression.arrow α)) (funUncurry (MorphismExpression.arrow β))) where
  module A = MorphismExpression α
  module B = MorphismExpression β
  δ = funIsoReflect A.arrow B.arrow θ

  endpoint : (x : Obj-abs [1]) {z : MAP Γ C}
    (p : =₁ (evaluate x ∘ A.arrow) z) (q : =₁ (evaluate x ∘ B.arrow) z) →
    =₂ ((q ∙ invIso (evaluate-uncurry x B.arrow)) ∙ (θ ▷ insert x))
      (p ∙ invIso (evaluate-uncurry x A.arrow)) → =₂ (q ∙ (evaluate x ◁ δ)) p
  endpoint x p q compatible = frame-square
    (evaluate-uncurry x A.arrow) (evaluate-uncurry x B.arrow) p q (evaluate x ◁ δ) (θ ▷ insert x)
    (isoComp-cong (preWhisker (insert x) ◁ funIsoReflect-β A.arrow B.arrow θ)
      (idIso (evaluate-uncurry x A.arrow)) ∙ Evaluation.natural x δ) compatible

  comparison :
    =₂ ((B.source-frame ∙ invIso (evaluate-uncurry zero B.arrow)) ∙ (θ ▷ insert zero))
      (A.source-frame ∙ invIso (evaluate-uncurry zero A.arrow)) →
    =₂ ((B.target-frame ∙ invIso (evaluate-uncurry one B.arrow)) ∙ (θ ▷ insert one))
      (A.target-frame ∙ invIso (evaluate-uncurry one A.arrow)) → ExpressionIso α β
  comparison source target = record
    { comparison = δ
    ; source-compatible = endpoint zero A.source-frame B.source-frame source
    ; target-compatible = endpoint one A.target-frame B.target-frame target }
```
