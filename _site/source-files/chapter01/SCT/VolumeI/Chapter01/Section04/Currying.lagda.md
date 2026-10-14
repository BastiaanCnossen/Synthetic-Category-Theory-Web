# The universal property of currying

The source `A`, identification parameter `X` and ambient context `Γ`
are independent. Only `A` needs to be an anima for recovery and currying.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Currying where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Boundaries using (SquareCell₌)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-reflect; equiv-compose; equiv-inverse)
open import SCT.VolumeI.Chapter01.Section03.Factorizations
  using (Factorization; factor; triangle; factor-through-equiv)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (factor-through-postWhisker; postcomp₌; precomp₌; postcomp₌-isEquiv;
    precomp₌-isEquiv; postcomp₌-evaluate; precomp₌-evaluate)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae

module _ {Γ : Context} {A C D : CAT Γ} where
  open Terms.InContext A using (Term)

  module _ {X : CAT Γ} where
    open Terms.Equalities X

    uncurry⁼ : {f g : Term (Map C D)} → f ＝ g → uncurry f ＝ uncurry g
    uncurry⁼ {f} {g} α = uncurry⁼-functor f g ∘ α

    uncurry⁼-cong : {f g : Term (Map C D)} {α β : f ＝ g}
      → α =₁ β → uncurry⁼ α =₁ uncurry⁼ β
    uncurry⁼-cong {f} {g} p = uncurry⁼-functor f g ◁ p
```

## Recovery with its specified image

The bundled recovery includes its factor and triangle. Reflection between
families and recovery of higher families use the generic equivalence toolkit.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X

    uncurry-reflection : (aAn : isAn A) (f g : Term (Map C D))
      (α : uncurry f ＝ uncurry g) → Factorization (uncurry⁼-functor f g) α
    uncurry-reflection aAn f g = factor-through-equiv (uncurry⁼-isEquiv aAn f g)

    uncurry-reflect : (aAn : isAn A) (f g : Term (Map C D))
      → uncurry f ＝ uncurry g → f ＝ g
    uncurry-reflect aAn f g α = factor (uncurry-reflection aAn f g α)

    uncurry-reflect-β : (aAn : isAn A) (f g : Term (Map C D))
      (α : uncurry f ＝ uncurry g) → uncurry⁼ (uncurry-reflect aAn f g α) =₁ α
    uncurry-reflect-β aAn f g α = triangle (uncurry-reflection aAn f g α)

    uncurry⁼-reflect : (aAn : isAn A) {f g : Term (Map C D)}
      (α β : f ＝ g) → uncurry⁼ α =₁ uncurry⁼ β → α =₁ β
    uncurry⁼-reflect aAn {f} {g} = equiv-reflect (uncurry⁼-isEquiv aAn f g)

    uncurry⁼-reflection : {Y : CAT Γ} (aAn : isAn A)
      {f g : Term (Map C D)} (α β : f ＝ g)
      (p : MAP Y (Equal (uncurry⁼ α) (uncurry⁼ β)))
      → Factorization (postWhisker (uncurry⁼-functor f g)) p
    uncurry⁼-reflection aAn {f} {g} α β p =
      factor-through-postWhisker (uncurry⁼-functor f g) (uncurry⁼-isEquiv aAn f g) p
```

## Curried representations

A representation itself does not require `isAn A`. The chosen construction
does. Comparing two representations recovers an identification from their
evaluation triangles; eta is the comparison with the given term.

```agda
  record CurriedRepresentation (h : MAP (A × C) D) : Set m where
    field
      term : Term (Map C D)
      evaluation : uncurry term =₁ h

  curried-representation : (aAn : isAn A) (h : MAP (A × C) D)
    → CurriedRepresentation h
  curried-representation aAn h = record
    { term = mapCurry aAn h; evaluation = mapCurry-β aAn h }

  representation-unique : (aAn : isAn A) {h : MAP (A × C) D}
    (r s : CurriedRepresentation h)
    → CurriedRepresentation.term r =₁ CurriedRepresentation.term s
  representation-unique aAn r s = uncurry-reflect aAn _ _
    ((CurriedRepresentation.evaluation s) ⁻¹ ∙ CurriedRepresentation.evaluation r)

  mapCurry-η : (aAn : isAn A) (f : Term (Map C D)) → mapCurry aAn (uncurry f) =₁ f
  mapCurry-η aAn f = representation-unique aAn
    (curried-representation aAn (uncurry f))
    (record { term = f; evaluation = id₌ (uncurry f) })
```

## Currying families and the evaluation square

The vertical sides are the fixed beta identifications. The square, rather
than only an expanded endpoint-change formula, is the public computation.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X

    curry⁼ : (aAn : isAn A) {h k : MAP (A × C) D}
      → h ＝ k → mapCurry aAn h ＝ mapCurry aAn k
    curry⁼ aAn {h} {k} α = uncurry-reflect aAn _ _
      ((const (mapCurry-β aAn k)) ⁻¹ ∙ (α ∙ const (mapCurry-β aAn h)))

    curry⁼-evaluation : (aAn : isAn A) {h k : MAP (A × C) D} (α : h ＝ k)
      → SquareCell₌ (uncurry⁼ (curry⁼ aAn α)) α
          (const (mapCurry-β aAn h)) (const (mapCurry-β aAn k))
    curry⁼-evaluation aAn {h} {k} α =
      comp-inv-left (const (mapCurry-β aAn k)) (α ∙ const (mapCurry-β aAn h)) ∙
        comp₌-cong (id₌ (const (mapCurry-β aAn k)))
          (uncurry-reflect-β aAn _ _
            ((const (mapCurry-β aAn k)) ⁻¹ ∙ (α ∙ const (mapCurry-β aAn h))))

    curry⁼-cong : (aAn : isAn A) {h k : MAP (A × C) D} {α β : h ＝ k}
      → α =₁ β → curry⁼ aAn α =₁ curry⁼ aAn β
    curry⁼-cong aAn {h} {k} p =
      IsEquiv.inverse (uncurry⁼-isEquiv aAn (mapCurry aAn h) (mapCurry aAn k)) ◁
        comp₌-cong (id₌ ((const (mapCurry-β aAn k)) ⁻¹))
          (comp₌-cong p (id₌ (const (mapCurry-β aAn h))))
```

## The actual currying action functor

Endpoint transport and inverse uncurrying form an equivalent functor on
identification animae. Its evaluation is identified with the already chosen
family action; associativity and constant inversion are not strict laws.

```agda
  curry⁼-functor : (aAn : isAn A) (h k : MAP (A × C) D)
    → MAP (Equal h k) (Equal (mapCurry aAn h) (mapCurry aAn k))
  curry⁼-functor aAn h k =
    IsEquiv.inverse (uncurry⁼-isEquiv aAn (mapCurry aAn h) (mapCurry aAn k)) ∘
      (postcomp₌ ((mapCurry-β aAn k) ⁻¹) ∘ precomp₌ (mapCurry-β aAn h))

  curry⁼-isEquiv : (aAn : isAn A) (h k : MAP (A × C) D)
    → IsEquiv (curry⁼-functor aAn h k)
  curry⁼-isEquiv aAn h k = equiv-compose
    (postcomp₌ ((mapCurry-β aAn k) ⁻¹) ∘ precomp₌ (mapCurry-β aAn h))
    (IsEquiv.inverse (uncurry⁼-isEquiv aAn (mapCurry aAn h) (mapCurry aAn k)))
    (equiv-compose (precomp₌ (mapCurry-β aAn h)) (postcomp₌ ((mapCurry-β aAn k) ⁻¹))
      (precomp₌-isEquiv (mapCurry-β aAn h)) (postcomp₌-isEquiv ((mapCurry-β aAn k) ⁻¹)))
    (equiv-inverse (uncurry⁼-isEquiv aAn (mapCurry aAn h) (mapCurry aAn k)))

  module _ {X : CAT Γ} where
    open Terms.Equalities X

    curry⁼-functor-evaluate : (aAn : isAn A) {h k : MAP (A × C) D} (α : h ＝ k)
      → (curry⁼-functor aAn h k ∘ α) =₁ curry⁼ aAn α
    curry⁼-functor-evaluate aAn {h} {k} α =
      let p = mapCurry-β aAn h
          q = mapCurry-β aAn k
          transport = postcomp₌ (q ⁻¹) ∘ precomp₌ p
          back = IsEquiv.inverse (uncurry⁼-isEquiv aAn (mapCurry aAn h) (mapCurry aAn k))
          endpoint-evaluation =
            comp₌-cong (const-inv q) (id₌ (α ∙ const p)) ∙
              (comp₌-cong (id₌ (const (q ⁻¹))) (precomp₌-evaluate p α) ∙
                (postcomp₌-evaluate (q ⁻¹) (precomp₌ p ∘ α) ∙
                  comp-assoc α (precomp₌ p) (postcomp₌ (q ⁻¹))))
      in (back ◁ endpoint-evaluation) ∙ comp-assoc α transport back
```

## Basic action and restriction laws

The product calculation computes the same primary action. Its identity and
composition laws transfer to that action through the evaluation equation.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X

    uncurry⁼-evaluate : {f g : Term (Map C D)} (α : f ＝ g)
      → uncurry⁼ α =₁ (mapEval ◁ productMap-cong α (const (id₌ (id C))))
    uncurry⁼-evaluate {f} {g} α =
      (postWhisker mapEval ◁
        (productMap-cong₂ (comp-unitˡ α) (const-pre (id₌ (id C)) α) ∙
          productMap-cong-pre (id (Equal f g)) (const (id₌ (id C))) α)) ∙
        comp-assoc α (productMap-cong (id (Equal f g)) (const (id₌ (id C))))
          (postWhisker mapEval)

    uncurry⁼-identity : (f : Term (Map C D))
      → uncurry⁼ (const {P = X} (id₌ f)) =₁ const (id₌ (uncurry f))
    uncurry⁼-identity f =
      const-cong (postWhisker-id₌ mapEval (productMap f (id C))) ∙
        (post-constant mapEval (id₌ (productMap f (id C))) ∙
          ((postWhisker mapEval ◁ productMap-cong-id f (id C)) ∙
            uncurry⁼-evaluate (const (id₌ f))))

    uncurry⁼-composition : {f g h : Term (Map C D)} (β : g ＝ h) (α : f ＝ g)
      → uncurry⁼ (β ∙ α) =₁ (uncurry⁼ β ∙ uncurry⁼ α)
    uncurry⁼-composition β α =
      let identity = const {P = X} (id₌ (id C))
      in (comp₌-cong (uncurry⁼-evaluate β) (uncurry⁼-evaluate α)) ⁻¹ ∙
        (postWhisker-comp₌ mapEval (productMap-cong β identity) (productMap-cong α identity) ∙
          ((postWhisker mapEval ◁
            (productMap-cong-comp β α identity identity ∙
              productMap-cong₂ (id₌ (β ∙ α)) ((comp₌-unitˡ identity) ⁻¹))) ∙
            uncurry⁼-evaluate (β ∙ α)))

    uncurry⁼-restrict : {Y : CAT Γ} {f g : Term (Map C D)}
      (α : f ＝ g) (r : MAP Y X) → (uncurry⁼ α ∘ r) =₁ uncurry⁼ (α ∘ r)
    uncurry⁼-restrict {f = f} {g} α r = comp-assoc r α (uncurry⁼-functor f g)

    uncurry⁼-constant : {f g : Term (Map C D)} (α : f =₁ g)
      → uncurry⁼ (const {P = X} α) =₁ const (uncurry⁼ α)
    uncurry⁼-constant {f} {g} α = (comp-assoc (terminate X) α (uncurry⁼-functor f g)) ⁻¹

  uncurry-restrict : {R : CAT Γ} (f : Term (Map C D)) (σ : MAP R A)
    → uncurry (f ∘ σ) =₁ (uncurry f ∘ productMap σ (id C))
  uncurry-restrict f σ =
    (comp-assoc (productMap σ (id C)) (productMap f (id C)) mapEval) ⁻¹ ∙
      (mapEval ◁ (productMap-cong (id₌ (f ∘ σ)) (comp-unitˡ (id C)) ∙
        productMap-comp σ f (id C) (id C)) ⁻¹)

module _ {Γ : Context} where
  uncurry-id : (C D : CAT Γ) → uncurry (id (Map C D)) =₁ mapEval {C = C} {D = D}
  uncurry-id C D = comp-unitʳ mapEval ∙ (mapEval ◁ productMap-id (Map C D) C)
```
