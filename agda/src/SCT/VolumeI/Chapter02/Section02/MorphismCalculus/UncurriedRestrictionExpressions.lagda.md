# Parameter restriction of uncurried expressions

Uncurrying a restricted transformation is restriction of its diagram.
The insertion comparison transports the endpoint frames and retains the
associator used in the definition of expression restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedRestrictionExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionEvaluation 𝒯 M ℱ
  using (evaluate-insertion; evaluate-uncurry-compose)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M
  using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module At {Γ Δ C : CAT} {f g : MAP Γ C} (α : MorphismExpression f g) (r : MAP Δ Γ) where
  module A = MorphismExpression α
  H = funUncurry A.arrow
  step = productMap r (id [1])
  comparison : funUncurry (MorphismExpression.arrow (restrict-expression α r)) =₁ (H ∘ step)
  comparison = funUncurry-restrict A.arrow r

  module Endpoint (z : Obj-abs [1]) {h : MAP Γ C} (p : (evaluate z ∘ A.arrow) =₁ h) where
    i = insert {X = Δ} z
    Q = evaluate-uncurry z A.arrow
    R = evaluate-uncurry z (A.arrow ∘ r)
    χ = evaluate-insertion H r z
    associator = (comp-assoc r A.arrow (evaluate z)) ⁻¹
    front = p ∙ Q ⁻¹
    frame : ((H ∘ step) ∘ i) =₁ (h ∘ r)
    frame = (front ▷ r) ∙ χ ⁻¹

    abstract
      moved : (χ ⁻¹ ∙ (comparison ▷ i)) =₂ (((Q ▷ r) ∙ associator) ∙ R ⁻¹)
      moved = move-square χ ((Q ▷ r) ∙ associator) (comparison ▷ i) R
        ((isoComp-assoc-at χ (Q ▷ r) associator ∙
          evaluate-uncurry-compose z A.arrow r) ⁻¹)

      compatible : (frame ∙ (comparison ▷ i)) =₂ (((p ▷ r) ∙ associator) ∙ R ⁻¹)
      compatible = isoComp-cong
          (isoComp-cong
            ((preWhisker r ◁ cancel-inverse-tail p Q) ∙
              (preWhisker-isoComp-at front Q r) ⁻¹)
            (idIso associator)) (idIso (R ⁻¹)) ∙
        isoComp-cong ((isoComp-assoc-at (front ▷ r) (Q ▷ r) associator) ⁻¹) (idIso (R ⁻¹)) ∙
        (isoComp-assoc-at (front ▷ r) ((Q ▷ r) ∙ associator) (R ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso (front ▷ r)) moved ∙
        isoComp-assoc-at (front ▷ r) (χ ⁻¹) (comparison ▷ i)

  module Source = Endpoint zero A.source-frame
  module Target = Endpoint one A.target-frame
```
