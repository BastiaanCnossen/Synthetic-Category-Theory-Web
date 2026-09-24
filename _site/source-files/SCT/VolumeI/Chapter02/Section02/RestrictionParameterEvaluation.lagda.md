# Restriction and evaluation of a parametrized diagram

This is the mixed comparison for the actual `funPre`, `evaluate-pre`,
and `evaluate-uncurry` definitions. We first evaluate the product square,
then transport its boundary through the chosen `funPre-β`. Finally,
compatibility with parameter composition removes the intermediate
uncurrying comparison. Every boundary identification is retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section02.InsertionRestrictionEvaluation as ProductEvaluation

module SCT.VolumeI.Chapter02.Section02.RestrictionParameterEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter02.Section02.InsertionEvaluation 𝒯 M ℱ
  using (evaluate-insertion; evaluate-uncurry-compose)
open import SCT.VolumeI.Chapter02.Section02.RestrictionInsertions 𝒯 M ℱ using (insertion)
open import SCT.VolumeI.Chapter01.Section04.SquareEvaluation 𝒯 M using (change-evaluation)
open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯 using (append-square)
open import SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus 𝒯 using (append-four)

module At {X A B C : CAT} (r : MAP A B) (h : MAP X (Fun B C)) (x : Obj-abs A) where
  Y = Fun B C
  R = funPre {D = C} r
  e = funEval {C = B} {D = C}
  U = funUncurry R
  HA = productMap h (id A)
  HB = productMap h (id B)
  LX = productMap (id X) r
  LY = productMap (id Y) r
  ix = insert {X = X} x
  iy = insert {X = Y} x
  χX = insertion X r x
  χY = insertion Y r x
  β = funPre-β {D = C} r
  u = funUncurry-restrict R h
  q = funPre-uncurry r h
  module Product = ProductEvaluation.At 𝒯 M ℱ e h r x

  at-target = evaluate-uncurry (r ∘ x) h
  vertex = (e ◁ χY) ▷ h
  evaluation-associator = comp-assoc iy LY e ▷ h
  beta-at-vertex = (β ▷ iy) ▷ h
  old-evaluation = evaluate-uncurry x R ▷ h
  family-associator = (comp-assoc h R (evaluate x)) ⁻¹
  tail = old-evaluation ∙ family-associator
  product-evaluation = evaluate-insertion (e ∘ LY) h x
  original-evaluation = evaluate-insertion U h x
  output-vertex = funUncurry h ◁ χX
  output-associator = comp-assoc ix LX (funUncurry h)
  prefix = output-vertex ∙ output-associator
  separation-image = Product.restriction-evaluation ▷ ix
  beta-image = (β ▷ HA) ▷ ix
  substitution-image = u ▷ ix
  input-evaluation = evaluate-uncurry x (R ∘ h)

  abstract
    beta-square : (product-evaluation ∙ beta-at-vertex) =₂ (beta-image ∙ original-evaluation)
    beta-square = change-evaluation β h HA ix iy (insert-natural h x)

    substitution-square : (original-evaluation ∙ tail) =₂ (substitution-image ∙ input-evaluation)
    substitution-square = (isoComp-assoc-at original-evaluation old-evaluation family-associator ∙
      evaluate-uncurry-compose x R h) ⁻¹

    product-square : (at-target ∙ (vertex ∙ evaluation-associator)) =₂
      (prefix ∙ (separation-image ∙ product-evaluation))
    product-square = (isoComp-assoc-at output-vertex output-associator
      (separation-image ∙ product-evaluation)) ⁻¹ ∙ Product.comparison

    pre-image : (evaluate-pre r x ▷ h) =₂
      (vertex ∙ (evaluation-associator ∙ (beta-at-vertex ∙ old-evaluation)))
    pre-image = isoComp-cong (idIso vertex)
        (isoComp-cong (idIso evaluation-associator)
          (preWhisker-isoComp-at (β ▷ iy) (evaluate-uncurry x R) h) ∙
          preWhisker-isoComp-at (comp-assoc iy LY e) ((β ▷ iy) ∙ evaluate-uncurry x R) h) ∙
      preWhisker-isoComp-at (e ◁ χY)
        (comp-assoc iy LY e ∙ ((β ▷ iy) ∙ evaluate-uncurry x R)) h

    uncurried-image : (q ▷ ix) =₂ (separation-image ∙ (beta-image ∙ substitution-image))
    uncurried-image = isoComp-cong (idIso separation-image)
        (preWhisker-isoComp-at (β ▷ HA) u ix) ∙
      (preWhisker-isoComp-at Product.restriction-evaluation ((β ▷ HA) ∙ u) ix ∙
      (preWhisker ix ◁
        ((isoComp-assoc-at ((comp-assoc LX HB e) ⁻¹)
          ((e ◁ productMap-separate h r) ∙ comp-assoc HA LY e) ((β ▷ HA) ∙ u)) ⁻¹ ∙
        isoComp-cong (idIso ((comp-assoc LX HB e) ⁻¹))
          ((isoComp-assoc-at (e ◁ productMap-separate h r) (comp-assoc HA LY e) ((β ▷ HA) ∙ u)) ⁻¹))))

    middle : (product-evaluation ∙ (beta-at-vertex ∙ tail)) =₂
      (beta-image ∙ (substitution-image ∙ input-evaluation))
    middle = isoComp-cong (idIso beta-image) substitution-square ∙
      append-square product-evaluation beta-at-vertex beta-image original-evaluation tail beta-square

    core : (at-target ∙ (vertex ∙ (evaluation-associator ∙ (beta-at-vertex ∙ tail)))) =₂
      (prefix ∙ (separation-image ∙ (beta-image ∙ (substitution-image ∙ input-evaluation))))
    core = isoComp-cong (idIso prefix) (isoComp-cong (idIso separation-image) middle) ∙
      (isoComp-cong (idIso prefix)
        (isoComp-assoc-at separation-image product-evaluation (beta-at-vertex ∙ tail)) ∙
      (append-square at-target (vertex ∙ evaluation-associator) prefix
        (separation-image ∙ product-evaluation) (beta-at-vertex ∙ tail) product-square ∙
        isoComp-cong (idIso at-target)
          ((isoComp-assoc-at vertex evaluation-associator (beta-at-vertex ∙ tail)) ⁻¹)))

    comparison :
      (evaluate-uncurry (r ∘ x) h ∙
        ((evaluate-pre r x ▷ h) ∙ (comp-assoc h (funPre r) (evaluate x)) ⁻¹)) =₂
      ((funUncurry h ◁ insertion X r x) ∙
        (comp-assoc (insert x) (productMap (id X) r) (funUncurry h) ∙
          ((funPre-uncurry r h ▷ insert x) ∙ evaluate-uncurry x (funPre r ∘ h))))
    comparison = isoComp-assoc-at output-vertex output-associator ((q ▷ ix) ∙ input-evaluation) ∙
      (isoComp-cong (idIso prefix)
        (isoComp-cong (uncurried-image ⁻¹) (idIso input-evaluation) ∙
        ((isoComp-assoc-at separation-image (beta-image ∙ substitution-image) input-evaluation) ⁻¹ ∙
          isoComp-cong (idIso separation-image)
            ((isoComp-assoc-at beta-image substitution-image input-evaluation) ⁻¹))) ∙
      (core ∙ isoComp-cong (idIso at-target)
        (append-four vertex evaluation-associator beta-at-vertex old-evaluation family-associator ∙
          isoComp-cong pre-image (idIso family-associator))))
```
