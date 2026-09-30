# Postcomposition and restriction of expressions

Restriction of a postcomposed expression agrees with postcomposition
of its restriction. The arrow comparison is the external associator;
the two endpoint equations follow from the corresponding calculation
for projection witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-boundary-normal)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯
  using (compose-base; lift-base; lift-compose; associator-square)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre)

private
  normal : {Γ C D : CAT} (v : Obj-abs [1]) (F : MAP C D)
    (h : MAP Γ (Ar C)) {x : MAP Γ C} (p : (evaluate v ∘ h) =₁ x) →
    post-boundary v F h p =₂
      compose-base (evaluate v) (funPost F) (evaluate-post v F) h (lift-base F (evaluate v) h p)
  normal v F h p =
    (isoComp-assoc-at (F ◁ p) (comp-assoc h (evaluate v) F)
      (transport-pre (evaluate v) (funPost F) (evaluate-post v F) h)) ⁻¹ ∙
    post-boundary-normal v F h p

module At {Γ Δ C D : CAT} (F : MAP C D) (r : MAP Δ Γ)
  {x y : MAP Γ C} (α : MorphismExpression x y) where
  private
    module A = MorphismExpression α
    h = A.arrow

    endpoint : (v : Obj-abs [1]) {z : MAP Γ C} (p : (evaluate v ∘ h) =₁ z) →
      (post-boundary v F (h ∘ r) (transport-pre (evaluate v) h p r) ∙
        (evaluate v ◁ comp-assoc r h (funPost F))) =₂
      (comp-assoc r z F ∙
        ((post-boundary v F h p ▷ r) ∙ (comp-assoc r (funPost F ∘ h) (evaluate v)) ⁻¹))
    endpoint v {z} p = source-step ∙
      associator-square (evaluate v) (funPost F) h r
        (evaluate-post v F) (lift-base F (evaluate v) h p) (comp-assoc r z F) ∙
      isoComp-cong target-step (idIso (evaluate v ◁ comp-assoc r h (funPost F)))
      where
      pr = transport-pre (evaluate v) h p r
      tail = transport-pre (F ∘ evaluate v) h (lift-base F (evaluate v) h p) r
      identity-lift : lift-base F z r (idIso (z ∘ r)) =₂ comp-assoc r z F
      identity-lift = isoComp-unitˡ-at (comp-assoc r z F) ∙
        isoComp-cong (postWhisker-idIso F (z ∘ r)) (idIso (comp-assoc r z F))
      inner : compose-base (F ∘ evaluate v) h (lift-base F (evaluate v) h p) r
        (comp-assoc r z F) =₂ lift-base F (evaluate v) (h ∘ r) pr
      inner =
        isoComp-cong (postWhisker F ◁ isoComp-unitˡ-at pr)
          (idIso (comp-assoc (h ∘ r) (evaluate v) F)) ∙
        lift-compose F (evaluate v) h r p (idIso (z ∘ r)) ∙
        isoComp-cong (identity-lift ⁻¹) (idIso tail)
      target-step =
        isoComp-cong (inner ⁻¹)
          (idIso (transport-pre (evaluate v) (funPost F) (evaluate-post v F) (h ∘ r))) ∙
        normal v F (h ∘ r) pr
      source-step = isoComp-cong (idIso (comp-assoc r z F))
        (isoComp-cong (preWhisker r ◁ (normal v F h p) ⁻¹)
          (idIso ((comp-assoc r (funPost F ∘ h) (evaluate v)) ⁻¹)))

  comparison : ExpressionIso
    (retarget-expression (restrict-expression (post-expression F α) r)
      (comp-assoc r x F) (comp-assoc r y F))
    (post-expression F (restrict-expression α r))
  comparison = record
    { comparison = comp-assoc r A.arrow (funPost F)
    ; source-compatible = endpoint zero A.source-frame
    ; target-compatible = endpoint one A.target-frame }

restrict-post : {Γ Δ C D : CAT} (F : MAP C D) {x y : MAP Γ C}
  (α : MorphismExpression x y) (r : MAP Δ Γ) →
  ExpressionIso
    (retarget-expression (restrict-expression (post-expression F α) r)
      (comp-assoc r x F) (comp-assoc r y F))
    (post-expression F (restrict-expression α r))
restrict-post F α r = At.comparison F r α
```
