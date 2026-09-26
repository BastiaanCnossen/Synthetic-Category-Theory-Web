# Composition of endpoint boundaries

The terminal-domain comparison used to convert restriction cones respects
composition. The proof combines restriction composition with naturality in
the chosen object; the right unitor removes the extra terminal identity.
Every boundary is the one already used in `EndpointRestrictionCones`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEndpointComposition as Composition
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointInputNaturality as Inputs
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as EndpointUnits

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointBoundaryComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (preComp)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (append-square)
open import SCT.VolumeI.Chapter01.Section04.Substitution.IsomorphismReasoning 𝒯
open EndpointUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (right-unitor-comp)

module At {A B C : CAT} (x : Obj-abs A) (f : MAP A B) where
  open PointBoundary C
  e = point-evaluation
  Rf = funPre {D = C} f
  Rx = funPre {D = C} x
  assoc = (comp-assoc Rf Rx e) ⁻¹
  q = evaluate-pre {C = C} x (id One)
  u = evaluate-cong {C = C} (comp-unitʳ x)
  v = evaluate-cong {C = C} (f ◁ comp-unitʳ x)
  b = evaluate-cong {C = C} (comp-assoc (id One) x f)
  t = evaluate-pre {C = C} f (x ∘ id One)
  w = evaluate-pre {C = C} (f ∘ x) (id One)
  κ = e ◁ preComp x f
  tail = (q ▷ Rf) ∙ assoc

  abstract
    vertex : (v ∙ b) =₂ evaluate-cong {C = C} (comp-unitʳ (f ∘ x))
    vertex = evaluate-cong-Iso₂ {C = C} ((right-unitor-comp x f) ⁻¹) ∙
      (evaluate-cong-comp {C = C} (f ◁ comp-unitʳ x) (comp-assoc (id One) x f)) ⁻¹

    expand-boundary : (evaluate-pre {C = C} f x ∙ ((boundary x ▷ Rf) ∙ assoc)) =₂
      (evaluate-pre {C = C} f x ∙ ((u ▷ Rf) ∙ tail))
    expand-boundary = isoComp-cong (idIso (evaluate-pre {C = C} f x))
      (isoComp-assoc-at (u ▷ Rf) (q ▷ Rf) assoc ∙
        isoComp-cong (preWhisker-isoComp-at u q Rf) (idIso assoc))

    change-object : (evaluate-pre {C = C} f x ∙ ((u ▷ Rf) ∙ tail)) =₂ (v ∙ (t ∙ tail))
    change-object = append-square (evaluate-pre {C = C} f x) (u ▷ Rf) v t tail
      (Inputs.RestrictionObject.natural 𝒯 M ℱ {C = C} f (comp-unitʳ x))

    compose-restrictions : (v ∙ (t ∙ tail)) =₂ (v ∙ (b ∙ (w ∙ κ)))
    compose-restrictions = isoComp-cong (idIso v)
      ((Composition.At.comparison 𝒯 M ℱ P {C = C} x f (id One)) ⁻¹)

    close-vertex : (v ∙ (b ∙ (w ∙ κ))) =₂ (boundary (f ∘ x) ∙ κ)
    close-vertex = (isoComp-assoc-at (evaluate-cong {C = C} (comp-unitʳ (f ∘ x))) w κ) ⁻¹ ∙
      (isoComp-cong vertex (idIso (w ∙ κ)) ∙
        (isoComp-assoc-at v b (w ∙ κ)) ⁻¹)

    normalize : (evaluate-pre {C = C} f x ∙ ((boundary x ▷ Rf) ∙ assoc)) =₂
      (boundary (f ∘ x) ∙ κ)
    normalize = begin₂
      (evaluate-pre {C = C} f x ∙ ((boundary x ▷ Rf) ∙ assoc))
        =₂⟨ expand-boundary ⟩
      (evaluate-pre {C = C} f x ∙ ((u ▷ Rf) ∙ tail))
        =₂⟨ change-object ⟩
      (v ∙ (t ∙ tail))
        =₂⟨ compose-restrictions ⟩
      (v ∙ (b ∙ (w ∙ κ)))
        =₂⟨ close-vertex ⟩
      (boundary (f ∘ x) ∙ κ) ∎₂

    comparison : (boundary (f ∘ x) ∙ (e ◁ preComp x f)) =₂
      (evaluate-pre {C = C} f x ∙
        ((boundary x ▷ funPre f) ∙ (comp-assoc (funPre f) (funPre x) e) ⁻¹))
    comparison = normalize ⁻¹
```
