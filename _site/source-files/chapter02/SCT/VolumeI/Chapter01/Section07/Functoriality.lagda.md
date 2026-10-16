# Functoriality of functor categories

Postcomposition and precomposition curry the corresponding evaluations.
Their formulas on arbitrary indexed functors retain the chosen beta
triangles. The family squares of these formulas are proved before the
identity, composition and equivalence laws. Precomposition reuses the
existing square for separating the two product coordinates.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.Functoriality where

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
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying

module _ {Γ : Context} where
  funPost : {C D E : CAT Γ} → MAP D E → MAP (Fun C D) (Fun C E)
  funPost {C} {D} {E} f = funCurry {C = C} {D = E} (f ∘ funEval {C = C} {D = D})

  funPre : {B C D : CAT Γ} → MAP B C → MAP (Fun C D) (Fun B D)
  funPre {B} {C} {D} k = funCurry {C = B} {D = D}
    (funEval {C = C} {D = D} ∘ productMap (id (Fun C D)) k)

  funPost-β : {C D E : CAT Γ} (f : MAP D E)
    → funUncurry {C = C} {D = E} (funPost {C = C} f) =₁ (f ∘ funEval {C = C} {D = D})
  funPost-β {C} {D} {E} f = funCurry-β {C = C} {D = E} (f ∘ funEval {C = C} {D = D})

  funPre-β : {B C D : CAT Γ} (k : MAP B C)
    → funUncurry {C = B} {D = D} (funPre {D = D} k) =₁
        (funEval {C = C} {D = D} ∘ productMap (id (Fun C D)) k)
  funPre-β {B} {C} {D} k = funCurry-β {C = B} {D = D}
    (funEval {C = C} {D = D} ∘ productMap (id (Fun C D)) k)

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    funPost⁼ : {C D E : CAT Γ} {f g : MAP D E}
      → f ＝ g → funPost {C = C} f ＝ funPost {C = C} g
    funPost⁼ {C} {D} {E} γ = curry⁼ (funEval {C = C} {D = E}) (funUniversal C E)
      (γ ▷ funEval {C = C} {D = D})

    funPre⁼ : {B C D : CAT Γ} {k l : MAP B C}
      → k ＝ l → funPre {D = D} k ＝ funPre {D = D} l
    funPre⁼ {B} {C} {D} γ = curry⁼ (funEval {C = B} {D = D}) (funUniversal B D)
      (funEval {C = C} {D = D} ◁ productMap-cong (const (id₌ (id (Fun C D)))) γ)

    funPost⁼-evaluation : {C D E : CAT Γ} {f g : MAP D E} (γ : f ＝ g)
      → SquareCell₌ (evaluate⁼ (funEval {C = C} {D = E}) (funPost⁼ {C = C} γ))
          (γ ▷ funEval {C = C} {D = D}) (const (funPost-β {C = C} f)) (const (funPost-β {C = C} g))
    funPost⁼-evaluation {C} {D} {E} γ =
      curry⁼-evaluation (funEval {C = C} {D = E}) (funUniversal C E)
        (γ ▷ funEval {C = C} {D = D})

    funPre⁼-evaluation : {B C D : CAT Γ} {k l : MAP B C} (γ : k ＝ l)
      → SquareCell₌ (evaluate⁼ (funEval {C = B} {D = D}) (funPre⁼ {D = D} γ))
          (funEval {C = C} {D = D} ◁ productMap-cong (const (id₌ (id (Fun C D)))) γ)
          (const (funPre-β {D = D} k)) (const (funPre-β {D = D} l))
    funPre⁼-evaluation {B} {C} {D} γ =
      curry⁼-evaluation (funEval {C = B} {D = D}) (funUniversal B D)
        (funEval {C = C} {D = D} ◁ productMap-cong (const (id₌ (id (Fun C D)))) γ)
```

## Evaluation on indexed functors

The parameter `T` is arbitrary. In the precomposition formula, the
coordinate-separation comparison retains both product-composition
comparisons and their unitors.

```agda
  funPost-uncurry : {T C D E : CAT Γ} (f : MAP D E) (g : MAP T (Fun C D))
    → funUncurry {C = C} {D = E} (funPost {C = C} f ∘ g) =₁
        (f ∘ funUncurry {C = C} {D = D} g)
  funPost-uncurry {C = C} {D} {E} f g =
    comp-assoc (productMap g (id C)) (funEval {C = C} {D = D}) f ∙
      ((funPost-β {C = C} f ▷ productMap g (id C)) ∙
        evaluate-restrict (funEval {C = C} {D = E}) (funPost {C = C} f) g)

  funPre-uncurry : {T B C D : CAT Γ} (k : MAP B C) (g : MAP T (Fun C D))
    → funUncurry {C = B} {D = D} (funPre {D = D} k ∘ g) =₁
        (funUncurry {C = C} {D = D} g ∘ productMap (id T) k)
  funPre-uncurry {T} {B} {C} {D} k g =
    (comp-assoc (productMap (id T) k) (productMap g (id C)) (funEval {C = C} {D = D})) ⁻¹ ∙
      ((funEval {C = C} {D = D} ◁ productMap-separate g k) ∙
        (comp-assoc (productMap g (id B)) (productMap (id (Fun C D)) k) (funEval {C = C} {D = D}) ∙
          ((funPre-β {D = D} k ▷ productMap g (id B)) ∙
            evaluate-restrict (funEval {C = B} {D = D}) (funPre {D = D} k) g)))
```

## Family squares of the evaluation triangles

The parameter `X` of a family of `T`-indexed functors is independent of
`T`. These are the full squares of the preceding chosen comparisons, with
native evaluation on both edges. Constant-side normalization is local to
this argument.

```agda
  private
    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
        {t : x ＝ y} {b : x′ ＝ y′} {u : x″ ＝ y″}
        {l : x =₁ x′} {r : y =₁ y′} {l′ : x′ =₁ x″} {r′ : y′ =₁ y″}
        → SquareCell₌ t b (const l) (const r) → SquareCell₌ b u (const l′) (const r′)
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

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    funPost-uncurry-inputs : {T C D E : CAT Γ} (f : MAP D E)
      {g h : MAP T (Fun C D)} (α : g ＝ h)
      → SquareCell₌ (evaluate⁼ (funEval {C = C} {D = E}) (funPost {C = C} f ◁ α))
          (f ◁ evaluate⁼ (funEval {C = C} {D = D}) α)
          (const (funPost-uncurry f g)) (const (funPost-uncurry f h))
    funPost-uncurry-inputs {C = C} {D} {E} f α = paste-fixed (paste-fixed
      (evaluate-restrict-substitution (funEval {C = C} {D = E}) (funPost {C = C} f) α)
      (interchange-fixedOuter (funPost-β {C = C} f) (productMap-cong α (const (id₌ (id C))))))
      (postWhisker-comp (productMap-cong α (const (id₌ (id C)))) (funEval {C = C} {D = D}) f)

    funPre-uncurry-inputs : {T B C D : CAT Γ} (k : MAP B C)
      {g h : MAP T (Fun C D)} (α : g ＝ h)
      → SquareCell₌ (evaluate⁼ (funEval {C = B} {D = D}) (funPre {D = D} k ◁ α))
          (evaluate⁼ (funEval {C = C} {D = D}) α ▷ productMap (id T) k)
          (const (funPre-uncurry k g)) (const (funPre-uncurry k h))
    funPre-uncurry-inputs {T} {B} {C} {D} k α = paste-fixed (paste-fixed (paste-fixed (paste-fixed
      (evaluate-restrict-substitution (funEval {C = B} {D = D}) (funPre {D = D} k) α)
      (interchange-fixedOuter (funPre-β {D = D} k) (productMap-cong α (const (id₌ (id B))))))
      (postWhisker-comp (productMap-cong α (const (id₌ (id B))))
        (productMap (id (Fun C D)) k) (funEval {C = C} {D = D})))
      (post-fixed (funEval {C = C} {D = D}) (productMap-separate-inputs α k)))
      (inverse-fixed (whisker-mixed (productMap-cong α (const (id₌ (id C))))
        (productMap (id T) k) (funEval {C = C} {D = D})))
```

## Identity and composition

Reflect the evaluated equations at the actual categorical test source.
The congruences below use the already chosen family actions at `One`;
there is no separate absolute recovery choice.

```agda
  funPost-cong : {C D E : CAT Γ} {f g : MAP D E}
    → f =₁ g → funPost {C = C} f =₁ funPost {C = C} g
  funPost-cong {C = C} = funPost⁼ {C = C}

  funPre-cong : {B C D : CAT Γ} {k l : MAP B C}
    → k =₁ l → funPre {D = D} k =₁ funPre {D = D} l
  funPre-cong {D = D} = funPre⁼ {D = D}

  funPost-id : (C D : CAT Γ) → funPost {C = C} (id D) =₁ id (Fun C D)
  funPost-id C D = reflect (funEval {C = C} {D = D}) (funUniversal C D) _ _
    ((evaluate-id (funEval {C = C} {D = D})) ⁻¹ ∙
      (comp-unitˡ (funEval {C = C} {D = D}) ∙ funPost-β {C = C} (id D)))

  funPre-id : (C D : CAT Γ) → funPre {D = D} (id C) =₁ id (Fun C D)
  funPre-id C D = reflect (funEval {C = C} {D = D}) (funUniversal C D) _ _
    ((evaluate-id (funEval {C = C} {D = D})) ⁻¹ ∙
      (comp-unitʳ (funEval {C = C} {D = D}) ∙
        ((funEval {C = C} {D = D} ◁ productMap-id (Fun C D) C) ∙ funPre-β {D = D} (id C))))

  funPost-comp : {A B C D : CAT Γ} (f : MAP B C) (g : MAP C D)
    → (funPost {C = A} g ∘ funPost {C = A} f) =₁ funPost {C = A} (g ∘ f)
  funPost-comp {A} {B} {C} {D} f g = reflect (funEval {C = A} {D = D}) (funUniversal A D) _ _
    ((funPost-β {C = A} (g ∘ f)) ⁻¹ ∙
      ((comp-assoc (funEval {C = A} {D = B}) f g) ⁻¹ ∙
        ((g ◁ funPost-β {C = A} f) ∙ funPost-uncurry g (funPost {C = A} f))))

  funPre-comp : {A B C D : CAT Γ} (f : MAP A B) (g : MAP B C)
    → (funPre {D = D} f ∘ funPre {D = D} g) =₁ funPre {D = D} (g ∘ f)
  funPre-comp {A} {B} {C} {D} f g = reflect (funEval {C = A} {D = D}) (funUniversal A D) _ _
    ((funPre-β {D = D} (g ∘ f)) ⁻¹ ∙
      ((funEval {C = C} {D = D} ◁
        (productMap-cong (comp-unitˡ (id (Fun C D))) (id₌ (g ∘ f)) ∙
          productMap-comp (id (Fun C D)) (id (Fun C D)) f g)) ∙
        (comp-assoc (productMap (id (Fun C D)) f) (productMap (id (Fun C D)) g)
          (funEval {C = C} {D = D}) ∙
          ((funPre-β {D = D} g ▷ productMap (id (Fun C D)) f) ∙ funPre-uncurry f (funPre {D = D} g)))))
```

## The two variables commute

Evaluate both composites to postcomposition after precomposition of the
original evaluation. Their specified beta comparisons, with one associator,
identify the two routes. Reflection gives the actual functor comparison.

```agda
  module _ {B C D E : CAT Γ} (k : MAP B C) (f : MAP D E) where
    private
      left-evaluation : funUncurry {C = B} {D = E}
        (funPre {D = E} k ∘ funPost {C = C} f) =₁
          (f ∘ (funEval {C = C} {D = D} ∘ productMap (id (Fun C D)) k))
      left-evaluation = comp-assoc (productMap (id (Fun C D)) k) (funEval {C = C} {D = D}) f ∙
        ((funPost-β {C = C} f ▷ productMap (id (Fun C D)) k) ∙ funPre-uncurry k (funPost {C = C} f))

      right-evaluation : funUncurry {C = B} {D = E}
        (funPost {C = B} f ∘ funPre {D = D} k) =₁
          (f ∘ (funEval {C = C} {D = D} ∘ productMap (id (Fun C D)) k))
      right-evaluation = (f ◁ funPre-β {D = D} k) ∙ funPost-uncurry f (funPre {D = D} k)

    funPost-funPre : (funPre {D = E} k ∘ funPost {C = C} f) =₁
      (funPost {C = B} f ∘ funPre {D = D} k)
    funPost-funPre = reflect (funEval {C = B} {D = E}) (funUniversal B E) _ _
      (right-evaluation ⁻¹ ∙ left-evaluation)
```

## Equivalences in either variable

Postcompose or precompose with the supplied inverse. The actual composition
laws, the chosen family congruences, and the identity laws give its two
inverse triangles.

```agda
  funPost-isEquiv : {A C D : CAT Γ} (f : MAP C D) → IsEquiv f
    → IsEquiv (funPost {C = A} f)
  funPost-isEquiv {A} {C} {D} f e = record
    { inverse = funPost {C = A} (IsEquiv.inverse e)
    ; left-inverse-law = (funPost-comp {A = A} f (IsEquiv.inverse e)) ⁻¹ ∙
        (funPost-cong {C = A} (IsEquiv.left-inverse-law e) ∙ (funPost-id A C) ⁻¹)
    ; right-inverse-law = (funPost-comp {A = A} (IsEquiv.inverse e) f) ⁻¹ ∙
        (funPost-cong {C = A} (IsEquiv.right-inverse-law e) ∙ (funPost-id A D) ⁻¹) }

  funPre-isEquiv : {C D E : CAT Γ} (f : MAP C D) → IsEquiv f
    → IsEquiv (funPre {D = E} f)
  funPre-isEquiv {C} {D} {E} f e = record
    { inverse = funPre {D = E} (IsEquiv.inverse e)
    ; left-inverse-law = (funPre-comp {D = E} (IsEquiv.inverse e) f) ⁻¹ ∙
        (funPre-cong {D = E} (IsEquiv.right-inverse-law e) ∙ (funPre-id D E) ⁻¹)
    ; right-inverse-law = (funPre-comp {D = E} f (IsEquiv.inverse e)) ⁻¹ ∙
        (funPre-cong {D = E} (IsEquiv.left-inverse-law e) ∙ (funPre-id C E) ⁻¹) }
```
