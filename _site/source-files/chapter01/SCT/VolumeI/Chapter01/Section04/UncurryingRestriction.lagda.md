# Uncurrying under restriction

Restricting a mapping term restricts its evaluated functor through the
product with the identity. The supplied comparison is natural both in the
term and in the restricting functor. Their family parameter is independent
of the term source; none of these squares requires that source to be an anima.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.UncurryingRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼; pair-pre)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution
  using (productMap-first-comp-assoc)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (solve-pentagon; preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (postWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-restriction-iterated; module CompositeEvaluation)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Functoriality

module _ {Γ : Context} {X : CAT Γ} where
  open Terms.Equalities X using (_＝_)

  private
    paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
      {t : x ＝ y} {m : x′ ＝ y′} {b : x″ ＝ y″}
      {l₁ : x =₁ x′} {r₁ : y =₁ y′} {l₂ : x′ =₁ x″} {r₂ : y′ =₁ y″}
      → SquareCell₌ t m (const l₁) (const r₁)
      → SquareCell₌ m b (const l₂) (const r₂)
      → SquareCell₌ t b (const (l₂ ∙ l₁)) (const (r₂ ∙ r₁))
    paste-fixed {l₁ = l₁} {r₁ = r₁} {l₂ = l₂} {r₂ = r₂} first second =
      replace-sides₌ (const-comp l₂ l₁) (const-comp r₂ r₁) (paste-square₌ first second)

    inverse-fixed : {A B : CAT Γ} {x y x′ y′ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b t (const (l ⁻¹)) (const (r ⁻¹))
    inverse-fixed {l = l} {r = r} square =
      replace-sides₌ ((const-inv l) ⁻¹) ((const-inv r) ⁻¹) (inverse-square₌ square)

  module _ {P C D : CAT Γ} where
    open Terms.InContext P using (Term)

    uncurry-restrict-inputs : {R : CAT Γ} {x y : Term (Map C D)} (α : x ＝ y) (r : MAP R P)
      → SquareCell₌ (uncurry⁼ (α ▷ r)) (uncurry⁼ α ▷ productMap r (id C))
          (const (uncurry-restrict x r)) (const (uncurry-restrict y r))
    uncurry-restrict-inputs {x = x} {y = y} α r =
      let R = productMap r (id C)
          pα = productMap-cong α (const (id₌ (id C)))
          first = replace-sides₌
            (post-constant mapEval ((productMap-first-comp x r) ⁻¹))
            (post-constant mapEval ((productMap-first-comp y r) ⁻¹))
            (post-square₌ mapEval (inverse-fixed (productMap-first-comp-inputs α r)))
          second = inverse-fixed (whisker-mixed pα R mapEval)
      in replace-edges₌ ((uncurry⁼-evaluate (α ▷ r)) ⁻¹)
          ((preWhisker R ◁ uncurry⁼-evaluate α) ⁻¹) (paste-fixed first second)

    uncurry-restrict-substitution : {R : CAT Γ} (x : Term (Map C D))
      {r s : MAP R P} (γ : r ＝ s)
      → SquareCell₌ (uncurry⁼ (x ◁ γ))
          (uncurry x ◁ productMap-cong γ (const (id₌ (id C))))
          (const (uncurry-restrict x r)) (const (uncurry-restrict x s))
    uncurry-restrict-substitution x {r = r} {s = s} γ =
      let pγ = productMap-cong γ (const (id₌ (id C)))
          first = replace-sides₌
            (post-constant mapEval ((productMap-first-comp x r) ⁻¹))
            (post-constant mapEval ((productMap-first-comp x s) ⁻¹))
            (post-square₌ mapEval (inverse-fixed (productMap-first-comp-substitution x γ)))
          second = inverse-fixed (postWhisker-comp pγ (productMap x (id C)) mapEval)
      in replace-edges₌ ((uncurry⁼-evaluate (x ◁ γ)) ⁻¹) (id₌ _) (paste-fixed first second)

    uncurry-restrict-natural : {R : CAT Γ} {x y : Term (Map C D)} {r s : MAP R P}
      (α : x ＝ y) (γ : r ＝ s)
      → SquareCell₌ (uncurry⁼ (α ⋆ γ))
          (uncurry⁼ α ⋆ productMap-cong γ (const (id₌ (id C))))
          (const (uncurry-restrict x r)) (const (uncurry-restrict y s))
    uncurry-restrict-natural {x = x} {s = s} α γ =
      replace-edges₌ ((uncurry⁼-composition (α ▷ s) (x ◁ γ)) ⁻¹) (id₌ _)
        (adjoin-square₌ (uncurry-restrict-substitution x γ) (uncurry-restrict-inputs α s))
```

Postcomposition uses the same restriction comparison, its specified
currying beta, and the associator. Pasting their squares computes the actual
uncurrying action on a varying term after postcomposition.

```agda
  module _ {P T C D : CAT Γ} where
    open Terms.InContext P using (Term)

    mapPost-uncurry-inputs : (f : MAP C D) {x y : Term (Map T C)} (α : x ＝ y)
      → SquareCell₌ (uncurry⁼ (mapPost f ◁ α)) (f ◁ uncurry⁼ α)
          (const (mapPost-uncurry f x)) (const (mapPost-uncurry f y))
    mapPost-uncurry-inputs f α =
      let pα = productMap-cong α (const (id₌ (id T)))
          first = uncurry-restrict-substitution (mapPost f) α
          second = interchange-fixedOuter (mapPost-β f) pα
          third = replace-edges₌ (id₌ _) ((postWhisker f ◁ uncurry⁼-evaluate α) ⁻¹)
            (postWhisker-comp pα mapEval f)
      in paste-fixed (paste-fixed first second) third
```


Successive restrictions preserve the chosen product-composition comparison.
The calculation uses its accepted associativity law and the generic
post-restriction pentagon. Only the individual identification calculation
normalizes the constant identity at `One`; the public action stays `uncurry⁼`.

```agda
module _ {Γ : Context} where
  private
    uncurry-action-One : {P C D : CAT Γ} {x y : MAP P (Map C D)} (α : x =₁ y)
      → uncurry⁼ α =₂ (mapEval ◁ productMap-cong α (id₌ (id C)))
    uncurry-action-One {C = C} α =
      (postWhisker mapEval ◁ productMap-cong₂ (id₌ α) (const-One (id₌ (id C)))) ∙
        uncurry⁼-evaluate α

    module RestrictionIteration {W Y X C D : CAT Γ}
      (x : MAP X (Map C D)) (σ : MAP Y X) (τ : MAP W Y) where

      F : {A B : CAT Γ} → MAP A B → MAP (A × C) (B × C)
      F h = productMap h (id C)

      change : {A B Z : CAT Γ} (h : MAP B Z) (r : MAP A B)
        → (F h ∘ F r) =₁ (F (h ∘ r))
      change = productMap-first-comp

      ProductAssociativity : Set m
      ProductAssociativity =
        (change x (σ ∘ τ) ∙ ((F x ◁ change σ τ) ∙ comp-assoc (F τ) (F σ) (F x))) =₂
        (productMap-cong (comp-assoc τ σ x) (id₌ (id C)) ∙
          (change (x ∘ σ) τ ∙ (change x σ ▷ F τ)))

      together : (uncurry ((x ∘ σ) ∘ τ)) =₁ (uncurry x ∘ F (σ ∘ τ))
      together = uncurry-restrict x (σ ∘ τ) ∙ uncurry⁼ (comp-assoc τ σ x)

      successively : (uncurry ((x ∘ σ) ∘ τ)) =₁ (uncurry x ∘ F (σ ∘ τ))
      successively = (uncurry x ◁ change σ τ) ∙
        (comp-assoc (F τ) (F σ) (uncurry x) ∙
          ((uncurry-restrict x σ ▷ F τ) ∙ uncurry-restrict (x ∘ σ) τ))

      transfer : ProductAssociativity → together =₂ successively
      transfer product-assoc =
        (comp₌-cong (id₌ (uncurry-restrict x (σ ∘ τ))) ((uncurry-action-One (comp-assoc τ σ x)) ⁻¹) ∙
        let p = F x
            s = F σ
            t = F τ
            e = mapEval
            k = change σ τ
            a = (change x σ) ⁻¹
            b = (change (x ∘ σ) τ) ⁻¹
            inner = comp-assoc t s p ∙ ((a ▷ t) ∙ b)
            outside = (comp-assoc (F (σ ∘ τ)) p e) ⁻¹
            middle = (comp-assoc (s ∘ t) p e) ⁻¹
            whiskered-k = p ◁ k
            associator = productMap-cong (comp-assoc τ σ x) (id₌ (id C))
            commute = (inverse-square₌ {t = uncurry x ◁ k} {b = e ◁ whiskered-k}
              {l = comp-assoc (s ∘ t) p e} {r = comp-assoc (F (σ ∘ τ)) p e}
              (postWhisker-comp-One k p e)) ⁻¹
            solve = solve-pentagon (change x (σ ∘ τ)) (whiskered-k ∙ comp-assoc t s p)
              associator (change (x ∘ σ) τ) (change x σ ▷ t)
              ((comp₌-assoc associator (change (x ∘ σ) τ) (change x σ ▷ t)) ⁻¹ ∙ product-assoc) ∙
              ((comp₌-assoc whiskered-k (comp-assoc t s p)
                ((change x σ ▷ t) ⁻¹ ∙ b)) ⁻¹ ∙
                comp₌-cong (id₌ whiskered-k)
                  (comp₌-cong (id₌ (comp-assoc t s p))
                    (comp₌-cong (preWhisker-inverse (change x σ) t) (id₌ b))))
        in (comp₌-assoc outside (e ◁ (change x (σ ∘ τ)) ⁻¹) (e ◁ associator)) ⁻¹ ∙
          (comp₌-cong (id₌ outside) (postWhisker-comp₌ e ((change x (σ ∘ τ)) ⁻¹) associator) ∙
          (comp₌-cong (id₌ outside) (postWhisker e ◁ solve) ∙
          (comp₌-cong (id₌ outside) ((postWhisker-comp₌ e whiskered-k inner) ⁻¹) ∙
          (comp₌-assoc outside (e ◁ whiskered-k) (e ◁ inner) ∙
          (comp₌-cong commute (id₌ (e ◁ inner)) ∙
          ((comp₌-assoc (uncurry x ◁ k) middle (e ◁ inner)) ⁻¹ ∙
            comp₌-cong (id₌ (uncurry x ◁ k))
              (post-restriction-iterated e p s t a b)))))))) ⁻¹

  module _ {P C D : CAT Γ} where
    open Terms.InContext P using (Term)

    uncurry-restrict-iterated : {W R : CAT Γ} (x : Term (Map C D))
      (r : MAP R P) (s : MAP W R)
      → (uncurry-restrict x (r ∘ s) ∙ uncurry⁼ (comp-assoc s r x)) =₂
          ((uncurry x ◁ productMap-first-comp r s) ∙
            (comp-assoc (productMap s (id C)) (productMap r (id C)) (uncurry x) ∙
              ((uncurry-restrict x r ▷ productMap s (id C)) ∙ uncurry-restrict (x ∘ r) s)))
    uncurry-restrict-iterated x r s = RestrictionIteration.transfer x r s
      (productMap-first-comp-assoc C x r s)
```

Postcomposition and restriction agree on their complete specified routes,
including the actual uncurrying action on the external associator. The
composite-evaluation transport supplies the beta part of the comparison.

```agda
module _ {Γ : Context} {P T C D : CAT Γ} where
  open Terms.InContext P using (Term)

  mapPost-uncurry-restrict : {Q : CAT Γ} (f : MAP C D)
    (x : Term (Map T C)) (r : MAP Q P) →
    ((f ◁ uncurry-restrict x r) ∙
      (mapPost-uncurry f (x ∘ r) ∙ uncurry⁼ (comp-assoc r x (mapPost f)))) =₂
      (comp-assoc (productMap r (id T)) (uncurry x) f ∙
        ((mapPost-uncurry f x ▷ productMap r (id T)) ∙ uncurry-restrict (mapPost f ∘ x) r))
  mapPost-uncurry-restrict {Q = Q₀} f x r =
    comp₌-cong (id₌ targetAssoc)
      (comp₌-cong ((preWhisker R ◁ comp₌-assoc (comp-assoc S mapEval f) (mapPost-β f ▷ S) (uncurry-restrict F x)) ∙
        (preWhisker-comp₌ (Eval.N S) (uncurry-restrict F x) R) ⁻¹) (id₌ y) ∙
        (comp₌-assoc (Eval.N S ▷ R) restricted y) ⁻¹) ∙
    (comp₌-assoc targetAssoc (Eval.N S ▷ R) K ∙
    (comp₌-cong core (id₌ K) ∙
    ((comp₌-assoc action (Eval.N Q ∙ (Aκ ∙ assocA)) K) ⁻¹ ∙
    (comp₌-cong (id₌ action)
      ((comp₌-assoc (Eval.N Q) (Aκ ∙ assocA) K) ⁻¹ ∙
        comp₌-cong (id₌ (Eval.N Q)) ((comp₌-assoc Aκ assocA K) ⁻¹)) ∙
    (comp₌-cong (id₌ action)
      (comp₌-cong (id₌ (Eval.N Q)) iteration ∙
        (comp₌-assoc (Eval.N Q) (uncurry-restrict F (x ∘ r)) (uncurry⁼ (comp-assoc r x F)) ∙
          comp₌-cong ((comp₌-assoc (comp-assoc Q mapEval f) (mapPost-β f ▷ Q) (uncurry-restrict F (x ∘ r))) ⁻¹)
            (id₌ (uncurry⁼ (comp-assoc r x F))))))))))
    where
    F : MAP (Map T C) (Map T D)
    F = mapPost f
    S : MAP (P × T) (Map T C × T)
    S = productMap x (id T)
    R : MAP (Q₀ × T) (P × T)
    R = productMap r (id T)
    Q : MAP (Q₀ × T) (Map T C × T)
    Q = productMap (x ∘ r) (id T)
    module Eval = CompositeEvaluation (mapEval {C = T} {D = C}) f (uncurry F) (mapPost-β f) S R Q (productMap-first-comp x r)
    action : (f ∘ uncurry (x ∘ r)) =₁ (f ∘ (uncurry x ∘ R))
    action = f ◁ uncurry-restrict x r
    Aκ : (uncurry F ∘ (S ∘ R)) =₁ (uncurry F ∘ Q)
    Aκ = uncurry F ◁ productMap-first-comp x r
    assocA : ((uncurry F ∘ S) ∘ R) =₁ (uncurry F ∘ (S ∘ R))
    assocA = comp-assoc R S (uncurry F)
    targetAssoc : ((f ∘ uncurry x) ∘ R) =₁ (f ∘ (uncurry x ∘ R))
    targetAssoc = comp-assoc R (uncurry x) f
    restricted : (uncurry (F ∘ x) ∘ R) =₁ ((uncurry F ∘ S) ∘ R)
    restricted = uncurry-restrict F x ▷ R
    y : (uncurry ((F ∘ x) ∘ r)) =₁ (uncurry (F ∘ x) ∘ R)
    y = uncurry-restrict (F ∘ x) r
    K : (uncurry ((F ∘ x) ∘ r)) =₁ ((uncurry F ∘ S) ∘ R)
    K = restricted ∙ y
    iteration : (uncurry-restrict F (x ∘ r) ∙ uncurry⁼ (comp-assoc r x F)) =₂
      (Aκ ∙ (assocA ∙ K))
    iteration = uncurry-restrict-iterated F x r
    core : (action ∙ (Eval.N Q ∙ (Aκ ∙ assocA))) =₂
      (targetAssoc ∙ (Eval.N S ▷ R))
    core = Eval.transport
```

The raw evaluation restriction compares the two supplied routes to common
coordinates. Relative lifts and their compatibility remain in
EvaluationRestriction; these chosen raw operations require no composition
comparison or recovery law.

```agda
module _ {Γ : Context} {P Q C D : CAT Γ} where
  open Terms.InContext P using (Term)
  module EvaluationChange (r : MAP Q P) where
    source-change = productMap r (id C)
    target-change = productMap r (id D)

    common : Term (Map C D) → MAP (Q × C) (P × D)
    common x = pair (r ∘ pr₁) (uncurry x ∘ source-change)

    input-normalization : (x : Term (Map C D))
      → pair (r ∘ pr₁) (id D ∘ uncurry (x ∘ r)) =₁ common x
    input-normalization x = pair⁼ (id₌ (r ∘ pr₁))
      (uncurry-restrict x r ∙ comp-unitˡ (uncurry (x ∘ r)))

    output-normalization : (x : Term (Map C D))
      → pair (pr₁ ∘ source-change) (uncurry x ∘ source-change) =₁ common x
    output-normalization x = pair⁼ (pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)) (id₌ _)

    input-route : (x : Term (Map C D))
      → (target-change ∘ pair pr₁ (uncurry (x ∘ r))) =₁ common x
    input-route x = input-normalization x ∙ productMap-pair r (id D) pr₁ (uncurry (x ∘ r))

    output-route : (x : Term (Map C D))
      → (pair pr₁ (uncurry x) ∘ source-change) =₁ common x
    output-route x = output-normalization x ∙ pair-pre pr₁ (uncurry x) source-change

    comparison : (x : Term (Map C D))
      → (target-change ∘ pair pr₁ (uncurry (x ∘ r))) =₁
        (pair pr₁ (uncurry x) ∘ source-change)
    comparison x = output-route x ⁻¹ ∙ input-route x
```
