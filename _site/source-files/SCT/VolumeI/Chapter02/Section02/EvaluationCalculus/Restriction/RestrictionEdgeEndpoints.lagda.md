# Normalizing the endpoints of a restricted edge

A face followed by a diagram gives an edge of the resulting family.
The theorem below evaluates a specified comparison of that edge and
retains its endpoint frame. Restriction composition and naturality are
used through their checked interfaces; the product diagram is not expanded.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionCompositorEvaluation as Retained
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEndpointComposition as Composition
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEdgeEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions 𝒯 M ℱ using (insertion)
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointCornerFamilies 𝒯 M ℱ P using (evaluate-cong-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (append-square)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

prefix : {A B C : CAT} (f : MAP A B) (x : Obj-abs A) →
  ((funEval ∘ productMap (id (Fun B C)) f) ∘ insert x) =₁ evaluate (f ∘ x)
prefix {B = B} {C = C} f x = (funEval ◁ insertion (Fun B C) f x) ∙
  comp-assoc (insert x) (productMap (id (Fun B C)) f) funEval

module Change {A B C : CAT} {f g : MAP A B} (α : f =₁ g) (x : Obj-abs A) where
  module R = Restriction {C = C} α x
  abstract
    comparison : (prefix {C = C} g x ∙ ((funEval ◁ R.image) ▷ R.i)) =₂
      (evaluate-cong {C = C} (α ▷ x) ∙ prefix f x)
    comparison = paste-squares
      (comp-assoc R.i R.F funEval) (comp-assoc R.i R.G funEval)
      (funEval ◁ (R.close-f ∙ productMap-pair (id R.X) f (id R.X) (const x)))
      (funEval ◁ (R.close-g ∙ productMap-pair (id R.X) g (id R.X) (const x)))
      ((funEval ◁ R.image) ▷ R.i) (funEval ◁ (R.image ▷ R.i)) (evaluate-cong (α ▷ x))
      (whisker-mixed-at R.image R.i funEval)
      (post-square funEval _ _ _ _ R.insertion-square)

module At {A B D C : CAT} (f : MAP A B) (g : MAP B D) (x : Obj-abs A)
  (r : MAP A D) (α : (g ∘ f) =₁ r) (z : Obj-abs D) (b : (r ∘ x) =₁ z) where
  module Raw = Retained.AtObject 𝒯 M ℱ P {C = C} f g x
  X = Fun D C
  e = funEval {C = D} {D = C}
  i = insert {X = X} x
  image = e ◁ productMap-cong (idIso (id X)) α
  Q = evaluate-uncurry x (funPre {D = C} f ∘ funPre g)
  rest = (Raw.leading ▷ i) ∙ Q
  old = prefix {C = C} (g ∘ f) x
  new = prefix {C = C} r x
  va = evaluate-cong {C = C} (comp-assoc x f g)
  vb = evaluate-cong {C = C} b
  vα = evaluate-cong {C = C} (α ▷ x)
  route = evaluate-pre {C = C} g (f ∘ x) ∙
    ((evaluate-pre f x ▷ funPre g) ∙ (comp-assoc (funPre g) (funPre f) (evaluate x)) ⁻¹)
  endpoint = b ∙ ((α ▷ x) ∙ (comp-assoc x f g) ⁻¹)

  abstract
    compose-edge : (va ∙ (old ∙ rest)) =₂ route
    compose-edge = Composition.At.comparison 𝒯 M ℱ P {C = C} f g x ∙
      isoComp-cong (idIso va) (Raw.comparison ⁻¹)

    remove-vertex : (old ∙ rest) =₂ (va ⁻¹ ∙ route)
    remove-vertex = isoComp-cong (idIso (va ⁻¹)) compose-edge ∙
      (cancel-left va (old ∙ rest)) ⁻¹

    endpoint-image : evaluate-cong {C = C} endpoint =₂ (vb ∙ (vα ∙ va ⁻¹))
    endpoint-image = isoComp-cong (idIso vb)
        (isoComp-cong (idIso vα) (evaluate-cong-inverse (comp-assoc x f g)) ∙
          evaluate-cong-comp (α ▷ x) ((comp-assoc x f g) ⁻¹)) ∙
      evaluate-cong-comp b ((α ▷ x) ∙ (comp-assoc x f g) ⁻¹)

  module Output {H : MAP (X × A) C}
    (out : (e ∘ productMap (id X) r) =₁ H)
    (finish : (H ∘ i) =₁ evaluate {C = C} z)
    (base : (finish ∙ (out ▷ i)) =₂ (vb ∙ new)) where
    diagram = out ∙ (image ∙ Raw.leading)
    remaining = (image ▷ i) ∙ rest

    abstract
      expand : (finish ∙ ((diagram ▷ i) ∙ Q)) =₂ (vb ∙ (new ∙ remaining))
      expand = append-square finish (out ▷ i) vb new remaining base ∙
        isoComp-cong (idIso finish)
          (isoComp-cong (idIso (out ▷ i)) (isoComp-assoc-at (image ▷ i) (Raw.leading ▷ i) Q) ∙
          (isoComp-assoc-at (out ▷ i) ((image ▷ i) ∙ (Raw.leading ▷ i)) Q ∙
            isoComp-cong
              (isoComp-cong (idIso (out ▷ i)) (preWhisker-isoComp-at image Raw.leading i) ∙
                preWhisker-isoComp-at out (image ∙ Raw.leading) i) (idIso Q)))

      normalize : (finish ∙ ((diagram ▷ i) ∙ Q)) =₂
        (evaluate-cong {C = C} endpoint ∙ route)
      normalize = isoComp-cong (endpoint-image ⁻¹) (idIso route) ∙
        ((isoComp-assoc-at vb (vα ∙ va ⁻¹) route) ⁻¹ ∙
        (isoComp-cong (idIso vb) ((isoComp-assoc-at vα (va ⁻¹) route) ⁻¹) ∙
        (isoComp-cong (idIso vb) (isoComp-cong (idIso vα) remove-vertex) ∙
        (isoComp-cong (idIso vb)
          (append-square new (image ▷ i) vα old rest (Change.comparison {C = C} α x)) ∙
          expand))))
```
