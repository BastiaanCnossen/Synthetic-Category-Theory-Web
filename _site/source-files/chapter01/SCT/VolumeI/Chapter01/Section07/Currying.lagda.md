# Currying into a functor category

For any supplied evaluation with the functor-category universal property,
factor a functor through its evaluation-induced equivalence of mapping
animae. This is the single chosen curried representation. Its beta law
uses the represented evaluation comparison; uniqueness and eta recover
identifications through the actual native action. The term source and
identification-family parameter are arbitrary and independent.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.Currying where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-reflect)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-postWhisker)
open import SCT.VolumeI.Chapter01.Section04.MappingSpecialization
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories

module _ {Γ : Context} {F C D : CAT Γ} (e : MAP (F × C) D) where
  record CurriedRepresentation {T : CAT Γ} (f : MAP (T × C) D) : Set m where
    field
      term : MAP T F
      evaluation : evaluate e term =₁ f

  module _ (universal : IsFunctorCategory e) where
    private
      chosen-factor : {T : CAT Γ} (f : MAP (T × C) D)
        → SpecializationFactorization (evaluation-forward e T) f
      chosen-factor {T} f = factor-through-specialize-map (evaluation-forward e T) (universal T) f

    curry : {T : CAT Γ} → MAP (T × C) D → MAP T F
    curry f = SpecializationFactorization.factor (chosen-factor f)

    curry-β : {T : CAT Γ} (f : MAP (T × C) D) → evaluate e (curry f) =₁ f
    curry-β {T} f = SpecializationFactorization.triangle (chosen-factor f) ∙
      (evaluation-specialize e T (curry f)) ⁻¹

    curried-representation : {T : CAT Γ} (f : MAP (T × C) D) → CurriedRepresentation f
    curried-representation f = record { term = curry f; evaluation = curry-β f }
```

## Recovering families with their images

The representation square proves that the actual native action is an
equivalence. Its factorization retains the chosen inverse and the image
equation. Higher reflection uses the same action, rather than substituting
a different recovery witness.

```agda
    module _ {X T : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      evaluation-reflection : (f g : MAP T F) (α : evaluate e f ＝ evaluate e g)
        → Fact.Factorization (evaluation-action e f g) α
      evaluation-reflection f g = Fact.factor-through-equiv (evaluation-action-isEquiv e T (universal T) f g)

      reflect : (f g : MAP T F) → evaluate e f ＝ evaluate e g → f ＝ g
      reflect f g α = Fact.factor (evaluation-reflection f g α)

      reflect-β : (f g : MAP T F) (α : evaluate e f ＝ evaluate e g)
        → evaluate⁼ e (reflect f g α) =₁ α
      reflect-β f g α = Fact.triangle (evaluation-reflection f g α) ∙
        (evaluation-action-evaluate e (reflect f g α)) ⁻¹

      evaluation-reflect₂ : {f g : MAP T F} (α β : f ＝ g)
        → evaluate⁼ e α =₁ evaluate⁼ e β → α =₁ β
      evaluation-reflect₂ {f} {g} α β p =
        equiv-reflect (evaluation-action-isEquiv e T (universal T) f g) α β
          ((evaluation-action-evaluate e β) ⁻¹ ∙ (p ∙ evaluation-action-evaluate e α))

      evaluation-reflection₂ : {Y : CAT Γ} {f g : MAP T F} (α β : f ＝ g)
        (p : MAP Y (Equal (evaluation-action e f g ∘ α) (evaluation-action e f g ∘ β)))
        → Fact.Factorization (postWhisker (evaluation-action e f g)) p
      evaluation-reflection₂ {f = f} {g} α β p =
        factor-through-postWhisker (evaluation-action e f g)
          (evaluation-action-isEquiv e T (universal T) f g) {f = α} {g = β} p

      curry⁼ : {f g : MAP (T × C) D} → f ＝ g → curry f ＝ curry g
      curry⁼ {f} {g} α = reflect (curry f) (curry g)
        ((const (curry-β g)) ⁻¹ ∙ (α ∙ const (curry-β f)))

      curry⁼-evaluation : {f g : MAP (T × C) D} (α : f ＝ g)
        → SquareCell₌ (evaluate⁼ e (curry⁼ α)) α (const (curry-β f)) (const (curry-β g))
      curry⁼-evaluation {f} {g} α =
        comp-inv-left (const (curry-β g)) (α ∙ const (curry-β f)) ∙
          comp₌-cong (id₌ (const (curry-β g)))
            (reflect-β (curry f) (curry g) ((const (curry-β g)) ⁻¹ ∙ (α ∙ const (curry-β f))))
```

## Uniqueness, eta and substitution

Representations are compared by their specified evaluation triangles.
Substitution evaluates the restricted curried functor using its native
restriction law, and then uses the same recovery.

```agda
    representation-unique : {T : CAT Γ} {f : MAP (T × C) D}
      (r s : CurriedRepresentation f) → CurriedRepresentation.term r =₁ CurriedRepresentation.term s
    representation-unique r s = reflect _ _
      ((CurriedRepresentation.evaluation s) ⁻¹ ∙ CurriedRepresentation.evaluation r)

    curry-η : {T : CAT Γ} (g : MAP T F) → curry (evaluate e g) =₁ g
    curry-η g = representation-unique (curried-representation (evaluate e g))
      (record { term = g; evaluation = id₌ (evaluate e g) })

    reflect-β-One : {T : CAT Γ} (f g : MAP T F) (α : evaluate e f =₁ evaluate e g)
      → evaluate-cong e (reflect f g α) =₂ α
    reflect-β-One f g α = reflect-β f g α ∙ (evaluate⁼-absolute e (reflect f g α)) ⁻¹

    curry-restrict : {S T : CAT Γ} (f : MAP (T × C) D) (r : MAP S T)
      → curry (f ∘ productMap r (id C)) =₁ (curry f ∘ r)
    curry-restrict f r = reflect _ _
      ((evaluate-restrict e (curry f) r) ⁻¹ ∙
        ((curry-β f ▷ productMap r (id C)) ⁻¹ ∙ curry-β (f ∘ productMap r (id C))))
```

## Comparing two supplied functor categories

Curry the first evaluation into the second category. Its inverse curries
the second evaluation into the first. Evaluating their composites reduces
to the two chosen beta laws, so reflection proves both inverse laws.
The comparison retains its evaluation triangle, as required by
`prop:Uniqueness_Of_Functor_Categories`.

```agda
module _ {Γ : Context} {F G C D : CAT Γ}
  (e : MAP (F × C) D) (u : IsFunctorCategory e)
  (d : MAP (G × C) D) (v : IsFunctorCategory d) where

  functor-category-comparison : MAP F G
  functor-category-comparison = curry d v e

  functor-category-comparison-β : evaluate d functor-category-comparison =₁ e
  functor-category-comparison-β = curry-β d v e

  functor-category-comparison-isEquiv : IsEquiv functor-category-comparison
  functor-category-comparison-isEquiv = record
    { inverse = back; left-inverse-law = left ⁻¹; right-inverse-law = right ⁻¹ }
    where
    back : MAP G F
    back = curry e u d
    left : (back ∘ functor-category-comparison) =₁ id F
    left = reflect e u _ _
      ((evaluate-id e) ⁻¹ ∙
        (functor-category-comparison-β ∙
          ((curry-β e u d ▷ productMap functor-category-comparison (id C)) ∙
            evaluate-restrict e back functor-category-comparison)))
    right : (functor-category-comparison ∘ back) =₁ id G
    right = reflect d v _ _
      ((evaluate-id d) ⁻¹ ∙
        (curry-β e u d ∙
          ((functor-category-comparison-β ▷ productMap back (id C)) ∙
            evaluate-restrict d functor-category-comparison back)))
```

## The chosen functor category

These operations specialize the same construction to `Fun C D` and its
specified evaluation. They introduce no further choice of inverse.

```agda
module _ {Γ : Context} {C D : CAT Γ} where
  funUncurry : {T : CAT Γ} → MAP T (Fun C D) → MAP (T × C) D
  funUncurry = evaluate (funEval {C = C} {D = D})

  funCurry : {T : CAT Γ} → MAP (T × C) D → MAP T (Fun C D)
  funCurry = curry (funEval {C = C} {D = D}) (funUniversal C D)

  funCurry-β : {T : CAT Γ} (f : MAP (T × C) D) → funUncurry (funCurry f) =₁ f
  funCurry-β = curry-β (funEval {C = C} {D = D}) (funUniversal C D)

  funCurry-η : {T : CAT Γ} (g : MAP T (Fun C D)) → funCurry (funUncurry g) =₁ g
  funCurry-η = curry-η (funEval {C = C} {D = D}) (funUniversal C D)
```
