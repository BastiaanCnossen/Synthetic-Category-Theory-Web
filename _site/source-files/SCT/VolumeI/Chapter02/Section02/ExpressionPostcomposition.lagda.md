# Postcomposition of endpoint-preserving identifications

Postcomposition acts on morphism expressions and on their identifications.
The proof tracks the evaluation and uncurrying comparisons in the existing
`post-boundary` formula.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.ExpressionPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section01.EndpointNaturality 𝒯 M ℱ using (module Evaluation)
open import SCT.VolumeI.Chapter01.Section07.MappingCompatibility 𝒯 M ℱ using (funPost-uncurry-natural)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module Endpoint {Γ C D : CAT} (F : MAP C D) (z : Obj-abs [1])
  {h k : MAP Γ (Ar C)} (α : h =₁ k) where
  i = insert {X = Γ} z
  u = funUncurryIso α
  v = funUncurryIso (funPost F ◁ α)
  φh = funPost-uncurry F h
  φk = funPost-uncurry F k
  Qh = evaluate-uncurry z h
  Qk = evaluate-uncurry z k
  Rh = evaluate-uncurry z (funPost F ∘ h)
  Rk = evaluate-uncurry z (funPost F ∘ k)
  Ah = comp-assoc i (funUncurry h) F
  Ak = comp-assoc i (funUncurry k) F
  Th = Ah ∙ ((φh ▷ i) ∙ Rh)
  Tk = Ak ∙ ((φk ▷ i) ∙ Rk)
  δ = evaluate z ◁ α
  δF = evaluate z ◁ (funPost F ◁ α)
  d = u ▷ i

  abstract
    image-square : ((φk ▷ i) ∙ (v ▷ i)) =₂ (((F ◁ u) ▷ i) ∙ (φh ▷ i))
    image-square = preWhisker-isoComp-at (F ◁ u) φh i ∙
      (preWhisker i ◁ funPost-uncurry-natural F α) ∙
      (preWhisker-isoComp-at φk v i) ⁻¹

    evaluation-square : (Tk ∙ δF) =₂ ((F ◁ d) ∙ Th)
    evaluation-square = paste-squares ((φh ▷ i) ∙ Rh) ((φk ▷ i) ∙ Rk)
      Ah Ak δF ((F ◁ u) ▷ i) (F ◁ d)
      (paste-squares Rh Rk (φh ▷ i) (φk ▷ i) δF (v ▷ i) ((F ◁ u) ▷ i)
        (Evaluation.natural z (funPost F ◁ α)) image-square)
      (whisker-mixed-at u i F)

    boundary-square : {x : MAP Γ C} (p : (evaluate z ∘ h) =₁ x) (q : (evaluate z ∘ k) =₁ x) →
      (q ∙ δ) =₂ p →
      (post-boundary z F k q ∙ δF) =₂ post-boundary z F h p
    boundary-square p q same =
      isoComp-cong post-raw (idIso Th) ∙
      (isoComp-assoc-at (F ◁ (q ∙ Qk ⁻¹)) (F ◁ d) Th) ⁻¹ ∙
      isoComp-cong (idIso (F ◁ (q ∙ Qk ⁻¹))) evaluation-square ∙
      isoComp-assoc-at (F ◁ (q ∙ Qk ⁻¹)) Tk δF
      where
      raw : ((q ∙ Qk ⁻¹) ∙ d) =₂ (p ∙ Qh ⁻¹)
      raw = isoComp-unitˡ-at (p ∙ Qh ⁻¹) ∙
        paste-squares (Qh ⁻¹) (Qk ⁻¹) p q d δ (idIso _)
          (move-square Qk δ d Qh (Evaluation.natural z α))
          ((isoComp-unitˡ-at p) ⁻¹ ∙ same)
      post-raw : ((F ◁ (q ∙ Qk ⁻¹)) ∙ (F ◁ d)) =₂ (F ◁ (p ∙ Qh ⁻¹))
      post-raw = (postWhisker F ◁ raw) ∙ (postWhisker-isoComp-at F (q ∙ Qk ⁻¹) d) ⁻¹

post-expressionIso : {Γ C D : CAT} (F : MAP C D) {x y : MAP Γ C}
  {f g : MorphismExpression x y} → ExpressionIso f g →
  ExpressionIso (post-expression F f) (post-expression F g)
post-expressionIso F {f = f} {g} α = record
  { comparison = funPost F ◁ ExpressionIso.comparison α
  ; source-compatible = Endpoint.boundary-square F zero (ExpressionIso.comparison α)
      (MorphismExpression.source-frame f) (MorphismExpression.source-frame g) (ExpressionIso.source-compatible α)
  ; target-compatible = Endpoint.boundary-square F one (ExpressionIso.comparison α)
      (MorphismExpression.target-frame f) (MorphismExpression.target-frame g) (ExpressionIso.target-compatible α) }
```

The boundary formula also agrees with postcomposing the original endpoint
frame and then using the specified evaluation comparison. This is the
form used for comparing whole triangle corners.

```agda
import SCT.VolumeI.Chapter02.Section02.PostcompositionParameterEvaluation as Parameter
open import SCT.VolumeI.Chapter01.Section04.ProductAssociativity 𝒯 M using (cancel-inverse-tail)

abstract
  post-boundary-normal : {Γ C D : CAT} (z : Obj-abs [1]) (F : MAP C D)
    (h : MAP Γ (Ar C)) {x : MAP Γ C} (p : (evaluate z ∘ h) =₁ x) →
    post-boundary z F h p =₂ ((F ◁ p) ∙ evaluate-post-at z F h)
  post-boundary-normal {Γ} {C} {D} z F h p =
    isoComp-cong ((postWhisker F ◁ cancel-inverse-tail p Q) ∙
      (postWhisker-isoComp-at F (p ∙ Q ⁻¹) Q) ⁻¹) (idIso R) ∙
    (isoComp-assoc-at (F ◁ (p ∙ Q ⁻¹)) (F ◁ Q) R) ⁻¹ ∙
    isoComp-cong (idIso (F ◁ (p ∙ Q ⁻¹))) (Parameter.At.comparison 𝒯 M ℱ F h z)
    where
    Q : (evaluate z ∘ h) =₁ (funUncurry h ∘ insert z)
    Q = evaluate-uncurry z h
    R : (evaluate z ∘ (funPost F ∘ h)) =₁ (F ∘ (evaluate z ∘ h))
    R = evaluate-post-at z F h

  post-evaluation-natural : {Γ C D : CAT} (z : Obj-abs [1]) (F : MAP C D)
    {h k : MAP Γ (Ar C)} (α : h =₁ k) →
    (evaluate-post-at z F k ∙ (evaluate z ◁ (funPost F ◁ α))) =₂
      ((F ◁ (evaluate z ◁ α)) ∙ evaluate-post-at z F h)
  post-evaluation-natural z F {h} {k} α = post-boundary-normal z F h (evaluate z ◁ α) ∙
    Endpoint.boundary-square F z α (evaluate z ◁ α) (idIso (evaluate z ∘ k))
      (isoComp-unitˡ-at (evaluate z ◁ α)) ∙
    isoComp-cong (normalize-id ⁻¹) (idIso (evaluate z ◁ (funPost F ◁ α)))
    where
    normalize-id : post-boundary z F k (idIso (evaluate z ∘ k)) =₂ evaluate-post-at z F k
    normalize-id = isoComp-unitˡ-at (evaluate-post-at z F k) ∙
      isoComp-cong (postWhisker-idIso F (evaluate z ∘ k)) (idIso (evaluate-post-at z F k)) ∙
      post-boundary-normal z F k (idIso (evaluate z ∘ k))
```
