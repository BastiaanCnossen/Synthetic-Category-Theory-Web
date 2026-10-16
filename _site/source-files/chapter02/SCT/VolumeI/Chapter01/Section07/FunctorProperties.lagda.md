# Elementary consequences of functor-category universality

The mapping-anima comparison is universal on anima sources. Its proof
uses the canonical core triangle and the core universal property, retaining
the hypothesis required by `prop:Mapping_Anima_Comparison`.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.FunctorProperties where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-compose; equiv-transport)
import SCT.VolumeI.Chapter01.Section04.Functoriality as Maps
open import SCT.VolumeI.Chapter01.Section04.Core using (coreInclusion; core-universal)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun

module _ {Γ : Context} where
  mappingInclusion-on-maps : (T C D : CAT Γ) → isAn T
    → IsEquiv (Maps.mapPost {C = T} (mappingInclusion C D))
  mappingInclusion-on-maps T C D tAn = equiv-transport
    (Maps.mapPost⁼ (coreFunComparison-inclusion C D) ∙
      Maps.mapPost-comp (coreFunComparison C D) (coreInclusion (Fun C D)))
    (equiv-compose (Maps.mapPost {C = T} (coreFunComparison C D))
      (Maps.mapPost {C = T} (coreInclusion (Fun C D)))
      (Maps.mapPost-isEquiv (coreFunComparison C D) (coreFunComparison-isEquiv C D))
      (core-universal T (Fun C D) tAn))
```

## Functors into the terminal category

The chosen terminal point curries the terminal functor. Reflection compares
every functor into `Fun C One` with that point after evaluation.

```agda
  funTerminalPoint : (C : CAT Γ) → MAP One (Fun C One)
  funTerminalPoint C = funCurry {C = C} {D = One} (terminate (One × C))

  funTerminal-isEquiv : (C : CAT Γ) → IsEquiv (terminate (Fun C One))
  funTerminal-isEquiv C = record
    { inverse = funTerminalPoint C
    ; left-inverse-law = (reflect (funEval {C = C} {D = One}) (funUniversal C One)
        (funTerminalPoint C ∘ terminate (Fun C One)) (id (Fun C One))
        (terminal-identification _ _)) ⁻¹
    ; right-inverse-law = terminal-identification _ _ }
```

## Functors from the terminal category

Evaluation at terminal insertion is inverse to currying the first
projection. Both inverse comparisons use the actual beta triangle.

```agda
  private
    evaluate-terminal : {F D T : CAT Γ} (e : MAP (F × One) D) (g : MAP T F)
      → ((e ∘ product-unitʳ-inverse F) ∘ g) =₁
          (evaluate e g ∘ product-unitʳ-inverse T)
    evaluate-terminal {F} {D} {T} e g =
      ((comp-assoc g (product-unitʳ-inverse F) e) ⁻¹ ∙
        ((e ◁ product-unitʳ-inverse-natural g) ∙
          comp-assoc (product-unitʳ-inverse T) (productMap g (id One)) e)) ⁻¹

  funOneEvaluation : (D : CAT Γ) → MAP (Fun One D) D
  funOneEvaluation D = funEval {C = One} {D = D} ∘ product-unitʳ-inverse (Fun One D)

  funOneInverse : (D : CAT Γ) → MAP D (Fun One D)
  funOneInverse D = funCurry {C = One} {D = D} pr₁

  funOneInverse-β : (D : CAT Γ)
    → funUncurry {C = One} {D = D} (funOneInverse D) =₁ pr₁
  funOneInverse-β D = funCurry-β {C = One} {D = D} pr₁

  funOneEvaluation-inverse : (D : CAT Γ)
    → (funOneEvaluation D ∘ funOneInverse D) =₁ id D
  funOneEvaluation-inverse D = pair-β₁ (id D) (terminate D) ∙
    ((funOneInverse-β D ▷ product-unitʳ-inverse D) ∙
      evaluate-terminal (funEval {C = One} {D = D}) (funOneInverse D))

  funOneInverse-evaluation : (D : CAT Γ)
    → (funOneInverse D ∘ funOneEvaluation D) =₁ id (Fun One D)
  funOneInverse-evaluation D = reflect e (funUniversal One D) _ _
    ((evaluate-id e) ⁻¹ ∙
      (comp-unitʳ e ∙
        ((e ◁ product-unitʳ-inverse-pr₁ F) ∙
          (comp-assoc pr₁ (product-unitʳ-inverse F) e ∙
            (pair-β₁ (funOneEvaluation D ∘ pr₁) (id One ∘ pr₂) ∙
              ((funOneInverse-β D ▷ productMap (funOneEvaluation D) (id One)) ∙
                evaluate-restrict e (funOneInverse D) (funOneEvaluation D)))))))
    where
    F : CAT Γ
    F = Fun One D
    e : MAP (F × One) D
    e = funEval {C = One} {D = D}

  funOneEvaluation-isEquiv : (D : CAT Γ) → IsEquiv (funOneEvaluation D)
  funOneEvaluation-isEquiv D = record
    { inverse = funOneInverse D
    ; left-inverse-law = (funOneInverse-evaluation D) ⁻¹
    ; right-inverse-law = (funOneEvaluation-inverse D) ⁻¹ }
```
