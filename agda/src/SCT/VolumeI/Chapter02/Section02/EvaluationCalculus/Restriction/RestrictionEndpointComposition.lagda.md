# Endpoint evaluation preserves the restriction compositor

The chosen compositor of `funPre` is evaluated using its retained
uncurried image. The mixed parameter theorem reduces successive endpoint
evaluation to the corresponding product diagram, whose composition law
was proved with the vertex associator retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionCompositorEvaluation as Retained
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionParameterEvaluation as Mixed
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertionCompositionEvaluation as Product

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEndpointComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (preComp)
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions 𝒯 M ℱ using (insertion)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (append-square)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationMateCalculus 𝒯 using (append-four)

module At {A B D C : CAT} (f : MAP A B) (g : MAP B D) (x : Obj-abs A) where
  module Raw = Retained.AtObject 𝒯 M ℱ P {C = C} f g x
    using (comparison; leading; prefix)
  X = Fun D C
  e = funEval {C = D} {D = C}
  F = productMap (id X) f
  G = productMap (id X) g
  i = insert {X = X} x
  j = insert {X = X} (f ∘ x)
  χf = insertion X f x
  χg = insertion X g (f ∘ x)
  Rg = funPre {D = C} g
  β = funPre-β {D = C} g
  q = funPre-uncurry f Rg
  Q = evaluate-uncurry x (funPre f ∘ Rg)
  vertex = evaluate-cong {C = C} (comp-assoc x f g)
  after-g = (e ◁ χg) ∙ comp-assoc j G e
  beta-at-point = β ▷ j
  old-action = funUncurry Rg ◁ χf
  old-associator = comp-assoc i F (funUncurry Rg)
  new-action = (e ∘ G) ◁ χf
  new-associator = comp-assoc i F (e ∘ G)
  beta-image = (β ▷ F) ▷ i
  tail = (q ▷ i) ∙ Q
  module Products = Product.At 𝒯 M ℱ X e f g x
  source-tail = (evaluate-pre f x ▷ Rg) ∙ (comp-assoc Rg (funPre f) (evaluate x)) ⁻¹
  right = evaluate-pre g (f ∘ x) ∙ source-tail
  common = vertex ∙ (Raw.prefix ∙ ((Raw.leading ▷ i) ∙ Q))

  abstract
    mixed-evaluation : right =₂
      (after-g ∙ (beta-at-point ∙ (old-action ∙ (old-associator ∙ tail))))
    mixed-evaluation = isoComp-cong (idIso after-g)
        (isoComp-cong (idIso beta-at-point) (Mixed.At.comparison 𝒯 M ℱ f Rg x)) ∙
      (isoComp-cong (idIso after-g)
        (isoComp-assoc-at beta-at-point (evaluate-uncurry (f ∘ x) Rg) source-tail) ∙
      (isoComp-assoc-at after-g (beta-at-point ∙ evaluate-uncurry (f ∘ x) Rg) source-tail ∙
        isoComp-cong ((isoComp-assoc-at (e ◁ χg) (comp-assoc j G e)
          (beta-at-point ∙ evaluate-uncurry (f ∘ x) Rg)) ⁻¹) (idIso source-tail)))

    move-beta :
      (after-g ∙ (beta-at-point ∙ (old-action ∙ (old-associator ∙ tail)))) =₂
      (Products.left ∙ (beta-image ∙ tail))
    move-beta = (isoComp-assoc-at (e ◁ χg) (comp-assoc j G e ∙ (new-action ∙ new-associator))
        (beta-image ∙ tail)) ⁻¹ ∙
      (isoComp-cong (idIso (e ◁ χg))
        ((isoComp-assoc-at (comp-assoc j G e) (new-action ∙ new-associator) (beta-image ∙ tail)) ⁻¹) ∙
      (isoComp-assoc-at (e ◁ χg) (comp-assoc j G e) ((new-action ∙ new-associator) ∙ (beta-image ∙ tail)) ∙
      isoComp-cong (idIso after-g)
        (append-square beta-at-point (old-action ∙ old-associator)
          (new-action ∙ new-associator) beta-image tail
          ((application-natural F i χf β) ⁻¹) ∙
          isoComp-cong (idIso beta-at-point) ((isoComp-assoc-at old-action old-associator tail) ⁻¹))))

    leading-image : (Raw.leading ▷ i) =₂ (Products.first-image ∙ (beta-image ∙ (q ▷ i)))
    leading-image = isoComp-cong (idIso Products.first-image) (preWhisker-isoComp-at (β ▷ F) q i) ∙
      (preWhisker-isoComp-at ((e ◁ Products.κ) ∙ comp-assoc F G e) ((β ▷ F) ∙ q) i ∙
      (preWhisker i ◁ ((isoComp-assoc-at (e ◁ Products.κ) (comp-assoc F G e) ((β ▷ F) ∙ q)) ⁻¹)))

    close-products : (Products.right ∙ (beta-image ∙ tail)) =₂ common
    close-products = isoComp-cong (idIso vertex)
        (isoComp-cong (idIso Raw.prefix)
          (isoComp-cong (leading-image ⁻¹) (idIso Q) ∙
          ((isoComp-assoc-at Products.first-image (beta-image ∙ (q ▷ i)) Q) ⁻¹ ∙
            isoComp-cong (idIso Products.first-image) ((isoComp-assoc-at beta-image (q ▷ i) Q) ⁻¹))) ∙
        (isoComp-assoc-at (e ◁ Products.χgf) (comp-assoc i Products.GF e)
          (Products.first-image ∙ (beta-image ∙ tail))) ⁻¹) ∙
      append-four vertex (e ◁ Products.χgf) (comp-assoc i Products.GF e)
        Products.first-image (beta-image ∙ tail)

    right-normalization : right =₂ common
    right-normalization = close-products ∙
      (isoComp-cong Products.comparison (idIso (beta-image ∙ tail)) ∙ (move-beta ∙ mixed-evaluation))

    comparison :
      (evaluate-cong {C = C} (comp-assoc x f g) ∙
        (evaluate-pre (g ∘ f) x ∙ (evaluate x ◁ preComp f g))) =₂
      (evaluate-pre g (f ∘ x) ∙
        ((evaluate-pre f x ▷ funPre g) ∙ (comp-assoc (funPre g) (funPre f) (evaluate x)) ⁻¹))
    comparison = right-normalization ⁻¹ ∙ isoComp-cong (idIso vertex) Raw.comparison
```
