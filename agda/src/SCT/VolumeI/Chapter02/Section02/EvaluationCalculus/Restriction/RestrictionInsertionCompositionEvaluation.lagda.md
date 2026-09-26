# Evaluating successive restrictions at a vertex

This is the forward form of the insertion composition law. The evaluation
functor is arbitrary, and both the product compositor and the associator
of the vertex remain visible in the conclusion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions as Insertions
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertionCompositionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open Insertions 𝒯 M ℱ using (insertion)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; whisker-mixed-at)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (append-square)

module At {A B D C : CAT} (X : CAT) (e : MAP (X × D) C)
  (f : MAP A B) (g : MAP B D) (x : Obj-abs A) where
  i = insert {X = X} x
  j = insert {X = X} (f ∘ x)
  F = productMap (id X) f
  G = productMap (id X) g
  GF = productMap (id X) (g ∘ f)
  χf = insertion X f x
  χg = insertion X g (f ∘ x)
  χgf = insertion X (g ∘ f) x
  κ = productRestriction-comp X f g
  vertex-associator = pair-cong (idIso (id X)) (comp-assoc x f g ▷ terminate X)
  first-image = ((e ◁ κ) ∙ comp-assoc F G e) ▷ i
  left = (e ◁ χg) ∙ (comp-assoc j G e ∙ (((e ∘ G) ◁ χf) ∙ comp-assoc i F (e ∘ G)))
  right = (e ◁ vertex-associator) ∙ ((e ◁ χgf) ∙ (comp-assoc i GF e ∙ first-image))
  product-path = χg ∙ ((G ◁ χf) ∙ comp-assoc i F G)
  alternative-path = vertex-associator ∙ (χgf ∙ (κ ▷ i))
  tail = comp-assoc i (G ∘ F) e ∙ (comp-assoc F G e ▷ i)

  abstract
    normalize-left : left =₂ ((e ◁ product-path) ∙ tail)
    normalize-left =
      isoComp-cong ((postWhisker-isoComp-at e χg ((G ◁ χf) ∙ comp-assoc i F G)) ⁻¹) (idIso tail) ∙
      ((isoComp-assoc-at (e ◁ χg) (e ◁ ((G ◁ χf) ∙ comp-assoc i F G)) tail) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ χg))
        (isoComp-cong ((postWhisker-isoComp-at e (G ◁ χf) (comp-assoc i F G)) ⁻¹) (idIso tail) ∙
        ((isoComp-assoc-at (e ◁ (G ◁ χf)) (e ◁ comp-assoc i F G) tail) ⁻¹ ∙
        (isoComp-cong (idIso (e ◁ (G ◁ χf))) (pentagon-whiskered i F G e) ∙
          append-square (comp-assoc j G e) ((e ∘ G) ◁ χf)
            (e ◁ (G ◁ χf)) (comp-assoc (F ∘ i) G e) (comp-assoc i F (e ∘ G))
            (postWhisker-comp-at χf G e)))))

    normalize-right : right =₂ ((e ◁ alternative-path) ∙ tail)
    normalize-right =
      isoComp-cong ((postWhisker-isoComp-at e vertex-associator (χgf ∙ (κ ▷ i))) ⁻¹) (idIso tail) ∙
      ((isoComp-assoc-at (e ◁ vertex-associator) (e ◁ (χgf ∙ (κ ▷ i))) tail) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ vertex-associator))
        (isoComp-cong ((postWhisker-isoComp-at e χgf (κ ▷ i)) ⁻¹) (idIso tail) ∙
        ((isoComp-assoc-at (e ◁ χgf) (e ◁ (κ ▷ i)) tail) ⁻¹ ∙
        isoComp-cong (idIso (e ◁ χgf))
          (append-square (comp-assoc i GF e) ((e ◁ κ) ▷ i)
            (e ◁ (κ ▷ i)) (comp-assoc i (G ∘ F) e) (comp-assoc F G e ▷ i)
            (whisker-mixed-at κ i e) ∙
          isoComp-cong (idIso (comp-assoc i GF e))
            (preWhisker-isoComp-at (e ◁ κ) (comp-assoc F G e) i)))))

    comparison : left =₂ right
    comparison = normalize-right ⁻¹ ∙
      (isoComp-cong (postWhisker e ◁ Insertions.Successive.law 𝒯 M ℱ X x f g) (idIso tail) ∙ normalize-left)
```
