# The core of a functor category

Evaluation at the terminal test category, followed by terminal insertion,
gives an equivalence `Core (Fun C D) → Map C D`. Its inverse compares the
mapping anima with the core. We retain the comparison with the canonical
inclusion and the actual evaluation, rather than only the equivalence of
the two animae (`core_of_Fun_is_Map`).

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.CoreOfFun where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; replace-sides₌; replace-edges₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-inverse)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Mapping
import SCT.VolumeI.Chapter01.Section04.Functoriality as Maps
open import SCT.VolumeI.Chapter01.Section04.Points
open import SCT.VolumeI.Chapter01.Section04.Core using (Core; coreInclusion)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluate-restrict-substitution)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-uncurry)

module _ {Γ : Context} where
  mappingInclusion : (C D : CAT Γ) → MAP (Map C D) (Fun C D)
  mappingInclusion C D = funCurry {C = C} {D = D} mapEval

  mappingInclusion-β : (C D : CAT Γ)
    → funUncurry {C = C} {D = D} (mappingInclusion C D) =₁ mapEval
  mappingInclusion-β C D = funCurry-β {C = C} {D = D} mapEval

  module _ (C D : CAT Γ) where
    coreFunUncurrying : MAP (Core (Fun C D)) (Map C D)
    coreFunUncurrying = Maps.mapPre (product-unitˡ-inverse C) ∘
      evaluation-forward (funEval {C = C} {D = D}) One

    coreFunUncurrying-isEquiv : IsEquiv coreFunUncurrying
    coreFunUncurrying-isEquiv = equiv-compose
      (evaluation-forward (funEval {C = C} {D = D}) One)
      (Maps.mapPre (product-unitˡ-inverse C)) (funUniversal C D One)
      (Maps.mapPre-isEquiv (product-unitˡ-inverse C) (product-unitˡ-inverse-isEquiv C))

    private
      A : CAT Γ
      A = Core (Fun C D)

      terminal-regroup :
        (Associativity.backward A One C ∘ productMap (id A) (product-unitˡ-inverse C)) =₁
          productMap (product-unitʳ-inverse A) (id C)
      terminal-regroup = right-normal ⁻¹ ∙ left-normal
        where
        k : MAP (A × C) (A × (One × C))
        k = productMap (id A) (product-unitˡ-inverse C)
        first : (pr₁ ∘ k) =₁ pr₁
        first = comp-unitˡ pr₁ ∙ pair-β₁ (id A ∘ pr₁) (product-unitˡ-inverse C ∘ pr₂)
        third : ((pr₂ ∘ pr₂) ∘ k) =₁ pr₂
        third = comp-unitˡ pr₂ ∙
          ((product-unitˡ-pr₂-inverse C ▷ pr₂) ∙
            ((comp-assoc pr₂ (product-unitˡ-inverse C) pr₂) ⁻¹ ∙
              ((pr₂ ◁ pair-β₂ (id A ∘ pr₁) (product-unitˡ-inverse C ∘ pr₂)) ∙ comp-assoc k pr₂ pr₂)))
        normal : MAP (A × C) ((A × One) × C)
        normal = pair (pair pr₁ (terminate (A × C))) pr₂
        left-normal : (Associativity.backward A One C ∘ k) =₁ normal
        left-normal = pair⁼
          (pair⁼ first (terminal-identification _ (terminate (A × C))) ∙ pair-pre pr₁ (pr₁ ∘ pr₂) k)
          third ∙ pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) k
        right-normal : productMap (product-unitʳ-inverse A) (id C) =₁ normal
        right-normal = pair⁼
          (pair⁼ (comp-unitˡ pr₁) (terminal-identification _ _) ∙ pair-pre (id A) (terminate A) pr₁)
          (comp-unitˡ pr₂)

    coreFunUncurrying-evaluation : uncurry coreFunUncurrying =₁
      funUncurry {C = C} {D = D} (coreInclusion (Fun C D))
    coreFunUncurrying-evaluation =
      (evaluate-restrict (funEval {C = C} {D = D}) mapEval (product-unitʳ-inverse A)) ⁻¹ ∙
        ((evaluate (funEval {C = C} {D = D}) mapEval ◁ terminal-regroup) ∙
          (comp-assoc (productMap (id A) (product-unitˡ-inverse C)) (Associativity.backward A One C)
            (evaluate (funEval {C = C} {D = D}) mapEval) ∙
            ((mapCurry-β (map-isAn One (Fun C D)) (evaluation-universal (funEval {C = C} {D = D}) One)
                ▷ productMap (id A) (product-unitˡ-inverse C)) ∙
              Maps.mapPre-uncurry (product-unitˡ-inverse C) (evaluation-forward (funEval {C = C} {D = D}) One))))

    mappingInclusion-coreUncurrying : (mappingInclusion C D ∘ coreFunUncurrying) =₁ coreInclusion (Fun C D)
    mappingInclusion-coreUncurrying = reflect (funEval {C = C} {D = D}) (funUniversal C D) _ _
      (coreFunUncurrying-evaluation ∙
        ((mappingInclusion-β C D ▷ productMap coreFunUncurrying (id C)) ∙
          evaluate-restrict (funEval {C = C} {D = D}) (mappingInclusion C D) coreFunUncurrying))

    coreFunComparison : MAP (Map C D) (Core (Fun C D))
    coreFunComparison = IsEquiv.inverse coreFunUncurrying-isEquiv

    coreFunComparison-isEquiv : IsEquiv coreFunComparison
    coreFunComparison-isEquiv = equiv-inverse coreFunUncurrying-isEquiv

    coreFunComparison-inclusion : (coreInclusion (Fun C D) ∘ coreFunComparison) =₁ mappingInclusion C D
    coreFunComparison-inclusion = comp-unitʳ (mappingInclusion C D) ∙
      ((mappingInclusion C D ◁ (IsEquiv.right-inverse-law coreFunUncurrying-isEquiv) ⁻¹) ∙
        (comp-assoc coreFunComparison coreFunUncurrying (mappingInclusion C D) ∙
          (mappingInclusion-coreUncurrying ⁻¹ ▷ coreFunComparison)))
```

## The inclusion on arbitrary indexed functors

Its evaluation comparison holds for every categorical source `T`. The full
family square compares native functor-category evaluation with the actual
mapping-anima action, including its evaluation normalization.

```agda
  mappingInclusion-uncurry : {T C D : CAT Γ} (g : MAP T (Map C D))
    → funUncurry {C = C} {D = D} (mappingInclusion C D ∘ g) =₁ uncurry g
  mappingInclusion-uncurry {C = C} {D} g = (mappingInclusion-β C D ▷ productMap g (id C)) ∙
    evaluate-restrict (funEval {C = C} {D = D}) (mappingInclusion C D) g

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    mappingInclusion-uncurry-inputs : {T C D : CAT Γ} {g h : MAP T (Map C D)} (α : g ＝ h)
      → SquareCell₌ (evaluate⁼ (funEval {C = C} {D = D}) (mappingInclusion C D ◁ α))
          (Mapping.uncurry⁼ α) (const (mappingInclusion-uncurry g)) (const (mappingInclusion-uncurry h))
    mappingInclusion-uncurry-inputs {C = C} {D} {g} {h} α =
      replace-edges₌ (id₌ (evaluate⁼ (funEval {C = C} {D = D}) (mappingInclusion C D ◁ α)))
        ((Mapping.uncurry⁼-evaluate α) ⁻¹)
        (replace-sides₌
          (const-comp (mappingInclusion-β C D ▷ productMap g (id C))
            (evaluate-restrict (funEval {C = C} {D = D}) (mappingInclusion C D) g))
          (const-comp (mappingInclusion-β C D ▷ productMap h (id C))
            (evaluate-restrict (funEval {C = C} {D = D}) (mappingInclusion C D) h))
          (paste-square₌
            (evaluate-restrict-substitution (funEval {C = C} {D = D}) (mappingInclusion C D) α)
            (interchange-fixedOuter (mappingInclusion-β C D) (productMap-cong α (const (id₌ (id C)))))))
```

## Actual postcomposition

Both composites evaluate to postcomposition of the mapping evaluation.
Their specified routes determine the inclusion comparison. Its native
image law retains that route, for clients which use the comparison in a
matching condition.

```agda
  module _ {C D E : CAT Γ} (f : MAP D E) where
    private
      left-route : funUncurry {C = C} {D = E} (funPost {C = C} f ∘ mappingInclusion C D) =₁
        (f ∘ mapEval {C = C} {D = D})
      left-route = (f ◁ mappingInclusion-β C D) ∙ funPost-uncurry f (mappingInclusion C D)

      right-route : funUncurry {C = C} {D = E} (mappingInclusion C E ∘ Maps.mapPost {C = C} f) =₁
        (f ∘ mapEval {C = C} {D = D})
      right-route = Maps.mapPost-β {C = C} f ∙ mappingInclusion-uncurry (Maps.mapPost {C = C} f)

    mappingInclusion-post-evaluation :
      funUncurry {C = C} {D = E} (funPost {C = C} f ∘ mappingInclusion C D) =₁
        funUncurry {C = C} {D = E} (mappingInclusion C E ∘ Maps.mapPost {C = C} f)
    mappingInclusion-post-evaluation = right-route ⁻¹ ∙ left-route

    mappingInclusion-post : (funPost {C = C} f ∘ mappingInclusion C D) =₁
      (mappingInclusion C E ∘ Maps.mapPost {C = C} f)
    mappingInclusion-post = reflect (funEval {C = C} {D = E}) (funUniversal C E) _ _
      mappingInclusion-post-evaluation

    mappingInclusion-post-image : evaluate-cong (funEval {C = C} {D = E}) mappingInclusion-post =₂
      mappingInclusion-post-evaluation
    mappingInclusion-post-image = reflect-β-One (funEval {C = C} {D = E}) (funUniversal C E) _ _
      mappingInclusion-post-evaluation
```

## Named points and the canonical core inclusion

The functor-category name curries the terminally indexed functor. Naming
in the mapping anima and then including gives this chosen point, by their
two evaluation triangles. The core comparison retains the resulting
canonical-inclusion triangle. Postcomposition uses the established
inclusion comparison and the existing mapping-anima naming law.

```agda
  funName : {C D : CAT Γ} → MAP C D → MAP One (Fun C D)
  funName {C} {D} g = funCurry {C = C} {D = D} (g ∘ pr₂ {C = One} {D = C})

  funName-β : {C D : CAT Γ} (g : MAP C D)
    → funUncurry {C = C} {D = D} (funName g) =₁ (g ∘ pr₂ {C = One} {D = C})
  funName-β {C} {D} g = funCurry-β {C = C} {D = D} (g ∘ pr₂ {C = One} {D = C})

  mappingInclusion-name : {C D : CAT Γ} (g : MAP C D)
    → (mappingInclusion C D ∘ name g) =₁ funName g
  mappingInclusion-name {C} {D} g = reflect (funEval {C = C} {D = D}) (funUniversal C D) _ _
    ((funName-β g) ⁻¹ ∙
      (Mapping.CurriedRepresentation.evaluation (name-representation g) ∙ mappingInclusion-uncurry (name g)))

  coreFunComparison-name : {C D : CAT Γ} (g : MAP C D)
    → (coreInclusion (Fun C D) ∘ (coreFunComparison C D ∘ name g)) =₁ funName g
  coreFunComparison-name {C} {D} g = mappingInclusion-name g ∙
    ((coreFunComparison-inclusion C D ▷ name g) ∙
      (comp-assoc (name g) (coreFunComparison C D) (coreInclusion (Fun C D))) ⁻¹)

  funName-post : {C D E : CAT Γ} (f : MAP D E) (g : MAP C D)
    → (funPost {C = C} f ∘ funName g) =₁ funName (f ∘ g)
  funName-post {C} {D} {E} f g = mappingInclusion-name (f ∘ g) ∙
    ((mappingInclusion C E ◁ Maps.mapPost-name f g) ∙
      (comp-assoc (name g) (Maps.mapPost {C = C} f) (mappingInclusion C E) ∙
        ((mappingInclusion-post {C = C} f ▷ name g) ∙
          ((comp-assoc (name g) (mappingInclusion C D) (funPost {C = C} f)) ⁻¹ ∙
            (funPost {C = C} f ◁ (mappingInclusion-name g) ⁻¹)))))
```
