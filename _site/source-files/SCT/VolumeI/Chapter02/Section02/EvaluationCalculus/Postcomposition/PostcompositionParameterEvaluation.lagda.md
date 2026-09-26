# Postcomposition and evaluation of a family

This compares the uncurried formula for postcomposition with the
specified evaluation comparison. It retains the parameter associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.PostcompositionParameterEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionEvaluation 𝒯 M ℱ
  using (evaluate-insertion; evaluate-uncurry-compose)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M using (change-evaluation)
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluationPostcomposition as Post

module At {Γ A C D : CAT} (F : MAP C D) (h : MAP Γ (Fun A C)) (z : Obj-abs A) where
  Y = Fun A C
  k = funPost {C = A} F
  e = funEval {C = A} {D = C}
  R = productMap h (id A)
  i = insert {X = Γ} z
  j = insert {X = Y} z
  β = funPost-β {C = A} F
  u = funUncurry-restrict k h
  φ = funPost-uncurry F h
  Q = evaluate-uncurry z (k ∘ h)
  Qk = evaluate-uncurry z k
  tail = (comp-assoc h k (evaluate z)) ⁻¹
  b = (β ▷ R) ▷ i
  v = comp-assoc i (e ∘ R) F
  w = comp-assoc R e F ▷ i
  original = evaluate-insertion (funUncurry k) h z
  changed = evaluate-insertion (F ∘ e) h z
  module Square = Post.At 𝒯 M e F h R i j (insert-natural h z)
  rest = (Qk ▷ h) ∙ tail

  abstract
    beta-square : (b ∙ original) =₂ (changed ∙ ((β ▷ j) ▷ h))
    beta-square = (change-evaluation β h R i j (insert-natural h z)) ⁻¹

    raw-image : ((φ ▷ i) ∙ Q) =₂
      (w ∙ ((b ∙ original) ∙ rest))
    raw-image = isoComp-cong (idIso w)
        ((isoComp-assoc-at b original rest) ⁻¹ ∙
          isoComp-cong (idIso b)
            (isoComp-assoc-at original (Qk ▷ h) tail ∙ evaluate-uncurry-compose z k h) ∙
          isoComp-assoc-at b (u ▷ i) Q ∙
          isoComp-cong (preWhisker-isoComp-at (β ▷ R) u i) (idIso Q)) ∙
      isoComp-assoc-at w (((β ▷ R) ∙ u) ▷ i) Q ∙
      isoComp-cong (preWhisker-isoComp-at (comp-assoc R e F) ((β ▷ R) ∙ u) i) (idIso Q)

    regroup : (v ∙ (w ∙ ((changed ∙ ((β ▷ j) ▷ h)) ∙ rest))) =₂
      (((v ∙ w) ∙ changed) ∙ ((((β ▷ j) ▷ h) ∙ (Qk ▷ h)) ∙ tail))
    regroup = isoComp-cong (idIso ((v ∙ w) ∙ changed))
        ((isoComp-assoc-at ((β ▷ j) ▷ h) (Qk ▷ h) tail) ⁻¹) ∙
      (isoComp-assoc-at (v ∙ w) changed (((β ▷ j) ▷ h) ∙ rest)) ⁻¹ ∙
      isoComp-cong (idIso (v ∙ w)) (isoComp-assoc-at changed ((β ▷ j) ▷ h) rest) ∙
      (isoComp-assoc-at v w ((changed ∙ ((β ▷ j) ▷ h)) ∙ rest)) ⁻¹

    endpoint-image : (evaluate-post z F ▷ h) =₂
      (Square.J₁ ∙ (((β ▷ j) ▷ h) ∙ (Qk ▷ h)))
    endpoint-image = isoComp-cong (idIso Square.J₁)
        (preWhisker-isoComp-at (β ▷ j) Qk h) ∙
      preWhisker-isoComp-at (comp-assoc j e F) ((β ▷ j) ∙ Qk) h

    comparison :
      (comp-assoc i (funUncurry h) F ∙ ((funPost-uncurry F h ▷ i) ∙ evaluate-uncurry z (funPost F ∘ h))) =₂
      ((F ◁ evaluate-uncurry z h) ∙ evaluate-post-at z F h)
    comparison = isoComp-cong (idIso (F ◁ evaluate-uncurry z h))
        (isoComp-cong (idIso Square.J₀)
          (isoComp-cong (endpoint-image ⁻¹) (idIso tail) ∙
            (isoComp-assoc-at Square.J₁ (((β ▷ j) ▷ h) ∙ (Qk ▷ h)) tail) ⁻¹) ∙
          isoComp-assoc-at Square.J₀ Square.J₁ ((((β ▷ j) ▷ h) ∙ (Qk ▷ h)) ∙ tail)) ∙
      isoComp-assoc-at (F ◁ evaluate-uncurry z h) Square.J ((((β ▷ j) ▷ h) ∙ (Qk ▷ h)) ∙ tail) ∙
      isoComp-cong (Square.comparison ⁻¹) (idIso ((((β ▷ j) ▷ h) ∙ (Qk ▷ h)) ∙ tail)) ∙
      regroup ∙
      isoComp-cong (idIso v) (isoComp-cong (idIso w) (isoComp-cong beta-square (idIso rest))) ∙
      isoComp-cong (idIso v) raw-image
```
