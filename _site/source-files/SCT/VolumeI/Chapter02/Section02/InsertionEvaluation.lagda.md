# Evaluation after successive parameter changes

Start with any functor `e : Z × A → C`. Evaluation at an inserted object
commutes with successive changes of parameter, retaining the specified
product compositor. Functor-category evaluation is a specialization of
this statement, rather than an extra coherence hypothesis.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section04.SquareEvaluation as Square
import SCT.VolumeI.Chapter02.Section02.InsertionParameterComposition as Insertion

module SCT.VolumeI.Chapter02.Section02.InsertionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ hiding (slice-comparison)
open import SCT.VolumeI.Chapter01.Section04.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting 𝒯 using (paste)
open Square 𝒯 M using (evaluate-square; evaluate-square-cong; change-bottom-inverse)

evaluate-insertion : {X Y A C : CAT} (e : MAP (Y × A) C) (h : MAP X Y) (x : Obj-abs A) →
  ((e ∘ insert x) ∘ h) =₁ ((e ∘ productMap h (id A)) ∘ insert x)
evaluate-insertion {A = A} e h x = evaluate-square e h (productMap h (id A))
  (insert x) (insert x) (insert-natural h x)

module Successive {X Y Z A C : CAT}
  (e : MAP (Z × A) C) (x : Obj-abs A) (h : MAP X Y) (k : MAP Y Z) where
  H = productMap h (id A)
  K = productMap k (id A)
  KH = productMap (k ∘ h) (id A)
  κ = slice-comparison {C = A} k h
  restriction = (comp-assoc H K e) ⁻¹ ∙ (e ◁ κ ⁻¹)
  module Pasted = Square.Pasting 𝒯 M e h k H K (insert x) (insert x) (insert x)
    (insert-natural h x) (insert-natural k x)

  abstract
    comparison :
      ((restriction ▷ insert x) ∙ evaluate-insertion e (k ∘ h) x) =₂
      ((evaluate-insertion (e ∘ K) h x ∙ (evaluate-insertion e k x ▷ h)) ∙
        (comp-assoc h k (e ∘ insert x)) ⁻¹)
    comparison = Pasted.comparison ∙
      (isoComp-cong (idIso ((comp-assoc H K e) ⁻¹ ▷ insert x))
        (change-bottom-inverse e (k ∘ h) (insert x) (insert x) κ
          (paste (insert-natural k x) (insert-natural h x)) ∙
          isoComp-cong (idIso ((e ◁ κ ⁻¹) ▷ insert x))
            (evaluate-square-cong e (k ∘ h) KH (insert x) (insert x) (Insertion.At.comparison 𝒯 M ℱ x h k))) ∙
      (isoComp-assoc-at ((comp-assoc H K e) ⁻¹ ▷ insert x)
        ((e ◁ κ ⁻¹) ▷ insert x) (evaluate-insertion e (k ∘ h) x) ∙
        isoComp-cong (preWhisker-isoComp-at ((comp-assoc H K e) ⁻¹) (e ◁ κ ⁻¹) (insert x))
          (idIso (evaluate-insertion e (k ∘ h) x))))

abstract
  evaluate-uncurry-compose : {X Y A C : CAT}
    (x : Obj-abs A) (k : MAP Y (Fun A C)) (h : MAP X Y) →
    ((funUncurry-restrict k h ▷ insert x) ∙ evaluate-uncurry x (k ∘ h)) =₂
      ((evaluate-insertion (funUncurry k) h x ∙ (evaluate-uncurry x k ▷ h)) ∙
        (comp-assoc h k (evaluate x)) ⁻¹)
  evaluate-uncurry-compose x k h = Successive.comparison funEval x h k
```
