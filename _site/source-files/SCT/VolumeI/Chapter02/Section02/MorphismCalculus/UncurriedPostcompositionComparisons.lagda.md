# Uncurried comparisons after postcomposition

A framed comparison after postcomposition identifies the corresponding
uncurried diagrams. The endpoint equation records the associator between
postcomposition and restriction. Retargeting at either endpoint remains
explicit, so this applies in particular to product projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedPostcompositionComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedExpressionComparisons as Uncurried
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M
  using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

abstract
  post-diagram-frame : {Γ C D : CAT} (F : MAP C D) (z : Obj-abs [1])
    (a₀ : MAP Γ (Ar C)) {h : MAP Γ C} (p : (evaluate z ∘ a₀) =₁ h) →
    (post-boundary z F a₀ p ∙ (evaluate-uncurry z (funPost F ∘ a₀)) ⁻¹) =₂
      ((F ◁ (p ∙ (evaluate-uncurry z a₀) ⁻¹)) ∙
        (comp-assoc (insert z) (funUncurry a₀) F ∙ (funPost-uncurry F a₀ ▷ insert z)))
  post-diagram-frame {Γ} {C} {D} F z a₀ {h} p =
    isoComp-cong (idIso front) (cancel-right Q (L ∙ v)) ∙
    isoComp-cong (idIso front)
      (isoComp-cong ((isoComp-assoc-at L v Q) ⁻¹) (idIso (Q ⁻¹))) ∙
    isoComp-assoc-at front (L ∙ (v ∙ Q)) (Q ⁻¹)
    where
    front : (F ∘ (funUncurry a₀ ∘ insert z)) =₁ (F ∘ h)
    front = F ◁ (p ∙ (evaluate-uncurry z a₀) ⁻¹)
    Q : (evaluate z ∘ (funPost F ∘ a₀)) =₁ (funUncurry (funPost F ∘ a₀) ∘ insert z)
    Q = evaluate-uncurry z (funPost F ∘ a₀)
    L : ((F ∘ funUncurry a₀) ∘ insert z) =₁ (F ∘ (funUncurry a₀ ∘ insert z))
    L = comp-assoc (insert z) (funUncurry a₀) F
    v : (funUncurry (funPost F ∘ a₀) ∘ insert z) =₁ ((F ∘ funUncurry a₀) ∘ insert z)
    v = funPost-uncurry F a₀ ▷ insert z

module At {Γ C D : CAT} {x y : MAP Γ C} {x′ y′ : MAP Γ D}
  (F : MAP C D) (α : MorphismExpression x y) (β : MorphismExpression x′ y′)
  (s : (F ∘ x) =₁ x′) (t : (F ∘ y) =₁ y′)
  (ξ : ExpressionIso (retarget-expression (post-expression F α) s t) β) where
  module A = MorphismExpression α
  module B = MorphismExpression β
  module U = Uncurried.UncurryComparison 𝒯 M ℱ P I E ξ
  H = funUncurry A.arrow
  K = funUncurry B.arrow
  post-comparison = funPost-uncurry F A.arrow
  comparison : (F ∘ H) =₁ K
  comparison = U.underlying ∙ post-comparison ⁻¹

  module Endpoint (z : Obj-abs [1]) {h : MAP Γ C} {k : MAP Γ D}
    (p : (evaluate z ∘ A.arrow) =₁ h)
    (q : (evaluate z ∘ B.arrow) =₁ k)
    (r : (F ∘ h) =₁ k)
    (same : (q ∙ (evaluate z ◁ ExpressionIso.comparison ξ)) =₂
      (r ∙ post-boundary z F A.arrow p)) where
    i = insert {X = Γ} z
    frontA = p ∙ (evaluate-uncurry z A.arrow) ⁻¹
    frontB = q ∙ (evaluate-uncurry z B.arrow) ⁻¹
    Q = evaluate-uncurry z (funPost F ∘ A.arrow)
    L = comp-assoc i H F
    v = post-comparison ▷ i
    w = U.underlying ▷ i

    abstract
      frame-normal : ((r ∙ post-boundary z F A.arrow p) ∙ Q ⁻¹) =₂
        (((r ∙ (F ◁ frontA)) ∙ L) ∙ v)
      frame-normal = (isoComp-assoc-at (r ∙ (F ◁ frontA)) L v) ⁻¹ ∙
        (isoComp-assoc-at r (F ◁ frontA) (L ∙ v)) ⁻¹ ∙
        isoComp-cong (idIso r) (post-diagram-frame F z A.arrow p) ∙
        isoComp-assoc-at r (post-boundary z F A.arrow p) (Q ⁻¹)

      compatible : (frontB ∙ (comparison ▷ i)) =₂ ((r ∙ (F ◁ frontA)) ∙ L)
      compatible = cancel-right-reflect v
        (frame-normal ∙ U.Endpoint.comparison z (r ∙ post-boundary z F A.arrow p) q same ∙
          isoComp-cong (idIso frontB)
            ((preWhisker i ◁ cancel-inverse-tail U.underlying post-comparison) ∙
              (preWhisker-isoComp-at comparison post-comparison i) ⁻¹) ∙
          isoComp-assoc-at frontB (comparison ▷ i) v)
```
