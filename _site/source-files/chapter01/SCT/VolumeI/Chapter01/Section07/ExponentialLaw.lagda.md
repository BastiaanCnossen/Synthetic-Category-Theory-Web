# The internal exponential law

The preferred comparison curries double evaluation. Its specified inverse
curries evaluation twice. Native evaluation and reflection compute both
inverse laws directly, for arbitrary categorical test sources. This proves
`lem:Internal_Adjunction_Product_Fun` without a separate mapping-test tower.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.ExponentialLaw where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution as Reassociation
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying

private
  module _ {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {u : x″ ＝ y″}
      {l : x =₁ x′} {r : y =₁ y′} {l′ : x′ =₁ x″} {r′ : y′ =₁ y″}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b u (const l′) (const r′)
      → SquareCell₌ t u (const (l′ ∙ l)) (const (r′ ∙ r))
    paste-fixed {l = l} {r} {l′} {r′} p q =
      replace-sides₌ (const-comp l′ l) (const-comp r′ r) (paste-square₌ p q)

    inverse-fixed : {A B : CAT Γ} {x y x′ y′ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b t (const (l ⁻¹)) (const (r ⁻¹))
    inverse-fixed {l = l} {r} p =
      replace-sides₌ ((const-inv l) ⁻¹) ((const-inv r) ⁻¹) (inverse-square₌ p)

    post-fixed : {A B Z : CAT Γ} (H : MAP B Z) {f g f′ g′ : MAP A B}
      {t : f ＝ g} {b : f′ ＝ g′} {l : f =₁ f′} {r : g =₁ g′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ (H ◁ t) (H ◁ b) (const (H ◁ l)) (const (H ◁ r))
    post-fixed H {l = l} {r} p =
      replace-sides₌ (post-constant H l) (post-constant H r) (post-square₌ H p)

    pre-fixed : {A B Z : CAT Γ} (k : MAP A B) {f g f′ g′ : MAP B Z}
      {t : f ＝ g} {b : f′ ＝ g′} {l : f =₁ f′} {r : g =₁ g′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ (t ▷ k) (b ▷ k) (const (l ▷ k)) (const (r ▷ k))
    pre-fixed k {l = l} {r} p =
      replace-sides₌ (pre-constant l k) (pre-constant r k) (pre-square₌ k p)


module ExponentialLaw {Γ : Context} (A B D : CAT Γ) where
  Nested : CAT Γ
  Nested = Fun A (Fun B D)
  Flat : CAT Γ
  Flat = Fun (A × B) D

  private
    eA : MAP (Nested × A) (Fun B D)
    eA = funEval {C = A} {D = Fun B D}
    eB : MAP (Fun B D × B) D
    eB = funEval {C = B} {D = D}
    eFlat : MAP (Flat × (A × B)) D
    eFlat = funEval {C = A × B} {D = D}

  doubleUncurry : {T : CAT Γ} → MAP T Nested → MAP ((T × A) × B) D
  doubleUncurry f = evaluate eB (evaluate eA f)

  doubleEvaluation : MAP ((Nested × A) × B) D
  doubleEvaluation = evaluate eB eA

  forwardEvaluation : MAP (Nested × (A × B)) D
  forwardEvaluation = doubleEvaluation ∘ Associativity.backward Nested A B

  forward : MAP Nested Flat
  forward = funCurry {C = A × B} {D = D} forwardEvaluation

  backwardEvaluation : MAP ((Flat × A) × B) D
  backwardEvaluation = eFlat ∘ Associativity.forward Flat A B

  backwardFirstCurry : MAP (Flat × A) (Fun B D)
  backwardFirstCurry = funCurry {C = B} {D = D} backwardEvaluation

  backward : MAP Flat Nested
  backward = funCurry {C = A} {D = Fun B D} backwardFirstCurry

  forward-β : evaluate eFlat forward =₁ forwardEvaluation
  forward-β = funCurry-β {C = A × B} {D = D} forwardEvaluation

  backward-β : doubleUncurry backward =₁ backwardEvaluation
  backward-β = funCurry-β {C = B} {D = D} backwardEvaluation ∙
    evaluate-cong eB (funCurry-β {C = A} {D = Fun B D} backwardFirstCurry)

  doubleUncurry-restrict : {R T : CAT Γ} (f : MAP T Nested) (σ : MAP R T)
    → doubleUncurry (f ∘ σ) =₁
        (doubleUncurry f ∘ productMap (productMap σ (id A)) (id B))
  doubleUncurry-restrict f σ = evaluate-restrict eB (evaluate eA f) (productMap σ (id A)) ∙
    evaluate-cong eB (evaluate-restrict eA f σ)

  doubleReflect : {T : CAT Γ} (f g : MAP T Nested)
    → doubleUncurry f =₁ doubleUncurry g → f =₁ g
  doubleReflect f g α = reflect eA (funUniversal A (Fun B D)) f g
    (reflect eB (funUniversal B D) (evaluate eA f) (evaluate eA g) α)

  doubleUncurry-id : doubleUncurry (id Nested) =₁ doubleEvaluation
  doubleUncurry-id = evaluate-cong eB (evaluate-id eA)
```

## Representing formulas

Substitution into each chosen comparison separates its beta computation
from the established reassociation comparison.

```agda
  forward-represents : {T : CAT Γ} (f : MAP T Nested)
    → evaluate eFlat (forward ∘ f) =₁
        (doubleUncurry f ∘ Associativity.backward T A B)
  forward-represents {T} f =
    (evaluate-restrict eB eA (productMap f (id A)) ⁻¹ ▷ regroup) ∙
      ((comp-assoc regroup changeTriple doubleEvaluation) ⁻¹ ∙
        ((doubleEvaluation ◁ Reassociation.backward-natural f) ∙
          (comp-assoc changePair (Associativity.backward Nested A B) doubleEvaluation ∙
            ((forward-β ▷ changePair) ∙ evaluate-restrict eFlat forward f))))
    where
    regroup = Associativity.backward T A B
    changePair = productMap f (id (A × B))
    changeTriple = productMap (productMap f (id A)) (id B)

  backward-represents : {T : CAT Γ} (f : MAP T Flat)
    → doubleUncurry (backward ∘ f) =₁
        (evaluate eFlat f ∘ Associativity.forward T A B)
  backward-represents {T} f =
    (comp-assoc regroup changePair eFlat) ⁻¹ ∙
      ((eFlat ◁ Reassociation.forward-natural f) ∙
        (comp-assoc changeTriple (Associativity.forward Flat A B) eFlat ∙
          ((backward-β ▷ changeTriple) ∙ doubleUncurry-restrict backward f)))
    where
    regroup = Associativity.forward T A B
    changePair = productMap f (id (A × B))
    changeTriple = productMap (productMap f (id A)) (id B)
```

## The specified inverse

The two inverse computations use the two associator inverse laws. They
establish the equivalence of the actual forward functor with the actual
double-curried backward functor as inverse.

```agda
  forward-backward : (forward ∘ backward) =₁ id Flat
  forward-backward = reflect eFlat (funUniversal (A × B) D) _ _
    ((evaluate-id eFlat) ⁻¹ ∙
      (comp-unitʳ eFlat ∙
        ((eFlat ◁ Associativity.forward-backward Flat A B) ∙
          (comp-assoc (Associativity.backward Flat A B) (Associativity.forward Flat A B) eFlat ∙
            ((backward-β ▷ Associativity.backward Flat A B) ∙ forward-represents backward)))))

  backward-forward : (backward ∘ forward) =₁ id Nested
  backward-forward = doubleReflect _ _
    (doubleUncurry-id ⁻¹ ∙
      (comp-unitʳ doubleEvaluation ∙
        ((doubleEvaluation ◁ Associativity.backward-forward Nested A B) ∙
          (comp-assoc (Associativity.forward Nested A B) (Associativity.backward Nested A B) doubleEvaluation ∙
            ((forward-β ▷ Associativity.forward Nested A B) ∙ backward-represents forward)))))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; left-inverse-law = backward-forward ⁻¹
    ; right-inverse-law = forward-backward ⁻¹ }
```

## The forward evaluation family

The full square follows the six factors of `forward-represents`. Its sides
are those literal chosen comparisons. The regrouping step reuses the
established product family square; objectwise representability alone would
not provide this boundary. No higher coherence of the inverse comparisons
is asserted here.

```agda
  module _ {X T : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    forward-represents-inputs : {f g : MAP T Nested} (α : f ＝ g)
      → SquareCell₌ (evaluate⁼ eFlat (forward ◁ α))
          (evaluate⁼ eB (evaluate⁼ eA α) ▷ Associativity.backward T A B)
          (const (forward-represents f)) (const (forward-represents g))
    forward-represents-inputs {f} {g} α =
      paste-fixed (paste-fixed (paste-fixed (paste-fixed (paste-fixed
        (evaluate-restrict-substitution eFlat forward α)
        (interchange-fixedOuter forward-β pairAction))
        (postWhisker-comp pairAction (Associativity.backward Nested A B) doubleEvaluation))
        (post-fixed doubleEvaluation (product-regroup-backward-inputs {T = A} {C = B} α)))
        (inverse-fixed (whisker-mixed tripleAction regroup doubleEvaluation)))
        (pre-fixed regroup (inverse-fixed (evaluate-restrict-substitution eB eA innerAction)))
      where
      regroup : MAP (T × (A × B)) ((T × A) × B)
      regroup = Associativity.backward T A B
      pairAction : MAP X (Equal (productMap f (id (A × B))) (productMap g (id (A × B))))
      pairAction = productMap-cong α (const (id₌ (id (A × B))))
      innerAction : MAP X (Equal (productMap f (id A)) (productMap g (id A)))
      innerAction = productMap-cong α (const (id₌ (id A)))
      tripleAction : MAP X (Equal (productMap (productMap f (id A)) (id B))
        (productMap (productMap g (id A)) (id B)))
      tripleAction = productMap-cong innerAction (const (id₌ (id B)))
```
