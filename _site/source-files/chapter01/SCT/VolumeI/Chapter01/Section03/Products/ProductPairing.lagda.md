# Product functors applied to pairs

Applying a product functor to a pair is computed coordinatewise:
`productMap-pair f g u v : productMap f g ∘ pair u v = pair (f ∘ u) (g ∘ v)`
is the paired evaluation of the two postcomposed projection laws. It lies
over its coordinates, it is natural in the product functor and in the pair,
and the projections of a product functor after an input functor are
computed by the same triangles.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.ProductPairing where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
```

## Evaluation at a pair

`productMap-pair f g u v` evaluates a product functor at a pair. Followed by
coordinate identifications `α : f ∘ x = x′` and `β : g ∘ y = y′`, it is the
evaluation `ProductPair.evaluation`; it is the paired evaluation of the
composite coordinates `first` and `second` (`normalization`) and therefore
lies over them (`evaluation-over₁`, `evaluation-over₂`).

```agda
module _ {Γ : Context} where
  module _ {R : CAT Γ} where
    open Terms.InContext R using (Term)

    productMap-pair : {C C′ D D′ : CAT Γ}
      (f : MAP C C′) (g : MAP D D′) (u : Term C) (v : Term D)
      → (productMap f g ∘ pair u v) =₁ pair (f ∘ u) (g ∘ v)
    productMap-pair f g u v =
      pair⁼ (post-triangle f pr₁ (pair u v) (pair-β₁ u v))
        (post-triangle g pr₂ (pair u v) (pair-β₂ u v)) ∙
      pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v)

  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities E using (_＝_)

    module ProductPair {A B C D : CAT Γ}
      (f : MAP A C) (g : MAP B D) (x : Term A) (y : Term B)
      {x′ : Term C} {y′ : Term D}
      (α : (f ∘ x) ＝ x′) (β : (g ∘ y) ＝ y′) where

      private
        left = post-triangle f pr₁ (pair x y) (pair-β₁ x y)
        right = post-triangle g pr₂ (pair x y) (pair-β₂ x y)
        pre = pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair x y)

      evaluation = pair⁼ α β ∙ const (productMap-pair f g x y)
      first = α ∙ const left
      second = β ∙ const right
      normalized = pair⁼ first second ∙ const pre

      abstract
        normalization : evaluation =₁ normalized
        normalization = comp₌-cong
          ((pair⁼-comp α (const left) β (const right)) ⁻¹) (id₌ (const pre)) ∙
          ((comp₌-assoc (pair⁼ α β) (pair⁼ (const left) (const right)) (const pre)) ⁻¹ ∙
            comp₌-cong (id₌ (pair⁼ α β))
              (comp₌-cong ((pair⁼-constant left right) ⁻¹) (id₌ (const pre)) ∙
                (const-comp (pair⁼ left right) pre) ⁻¹))

        evaluation-over₁ : SquareCell₌ (pr₁ ◁ evaluation) first
          (const (project-pair₁ (f ∘ pr₁) (g ∘ pr₂) (pair x y))) (const (pair-β₁ x′ y′))
        evaluation-over₁ = pair-evaluation-over₁ (f ∘ pr₁) (g ∘ pr₂) (pair x y) first second ∙
          comp₌-cong (id₌ (const (pair-β₁ x′ y′))) (postWhisker pr₁ ◁ normalization)

        evaluation-over₂ : SquareCell₌ (pr₂ ◁ evaluation) second
          (const (project-pair₂ (f ∘ pr₁) (g ∘ pr₂) (pair x y))) (const (pair-β₂ x′ y′))
        evaluation-over₂ = pair-evaluation-over₂ (f ∘ pr₁) (g ∘ pr₂) (pair x y) first second ∙
          comp₌-cong (id₌ (const (pair-β₂ x′ y′))) (postWhisker pr₂ ◁ normalization)

```

## Projections after an input functor

```agda
module _ {Γ : Context} where
  module _ {R : CAT Γ} where
    open Terms.InContext R using (Term)

    project-product₁ : {C C′ D D′ : CAT Γ}
      (f : MAP C C′) (g : MAP D D′) (u : Term (C × D))
      → (pr₁ ∘ (productMap f g ∘ u)) =₁ (f ∘ (pr₁ ∘ u))
    project-product₁ f g u = comp-assoc u pr₁ f ∙ project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u

    project-product₂ : {C C′ D D′ : CAT Γ}
      (f : MAP C C′) (g : MAP D D′) (u : Term (C × D))
      → (pr₂ ∘ (productMap f g ∘ u)) =₁ (g ∘ (pr₂ ∘ u))
    project-product₂ f g u = comp-assoc u pr₂ g ∙ project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u
```

## Naturality

```agda
module _ {Γ : Context} where
  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities E using (_＝_)

    productMap-pair-outer : {A B C D : CAT Γ}
      {f f′ : MAP A B} {g g′ : MAP C D}
      (α : f ＝ f′) (β : g ＝ g′) (p : Term A) (q : Term C)
      → SquareCell₌ (productMap-cong α β ▷ pair p q) (pair⁼ (α ▷ p) (β ▷ q))
          (const (productMap-pair f g p q)) (const (productMap-pair f′ g′ p q))
    productMap-pair-outer  {f = f} {f′} {g} {g′} α β p q =
      let t = pair p q
          b = pair-β₁ p q
          d = pair-β₂ p q
          left = post-triangle f pr₁ t b
          left′ = post-triangle f′ pr₁ t b
          right = post-triangle g pr₂ t d
          right′ = post-triangle g′ pr₂ t d
      in replace-sides₌ (pair-evaluation-const t left right)
        (pair-evaluation-const t left′ right′)
        (pair-evaluation-natural-inputs (α ▷ pr₁) (β ▷ pr₂) t
          (const left) (const left′) (const right) (const right′) (α ▷ p) (β ▷ q)
          (post-triangle-outer α pr₁ t b) (post-triangle-outer β pr₂ t d))

    productMap-pair-inner : {A B C D : CAT Γ} (f : MAP A B) (g : MAP C D)
      {p p′ : Term A} {q q′ : Term C} (σ : p ＝ p′) (τ : q ＝ q′)
      → SquareCell₌ (productMap f g ◁ pair⁼ σ τ) (pair⁼ (f ◁ σ) (g ◁ τ))
          (const (productMap-pair f g p q)) (const (productMap-pair f g p′ q′))
    productMap-pair-inner  f g {p} {p′} {q} {q′} σ τ =
      let t = pair p q
          t′ = pair p′ q′
          δ = pair⁼ σ τ
          left = post-triangle f pr₁ t (pair-β₁ p q)
          left′ = post-triangle f pr₁ t′ (pair-β₁ p′ q′)
          right = post-triangle g pr₂ t (pair-β₂ p q)
          right′ = post-triangle g pr₂ t′ (pair-β₂ p′ q′)
      in replace-sides₌ (pair-evaluation-const t left right)
        (pair-evaluation-const t′ left′ right′)
        (pair-evaluation-natural (f ∘ pr₁) (g ∘ pr₂) δ
          (const left) (const left′) (const right) (const right′) (f ◁ σ) (g ◁ τ)
          (post-triangle-inner f pr₁ δ σ (pair-β₁ p q) (pair-β₁ p′ q′) (pair⁼-triangle₁ σ τ))
          (post-triangle-inner g pr₂ δ τ (pair-β₂ p q) (pair-β₂ p′ q′) (pair⁼-triangle₂ σ τ)))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    productMap-pair-outer-One : {A B C D : CAT Γ}
      {f f′ : MAP A B} {g g′ : MAP C D}
      (α : f =₁ f′) (β : g =₁ g′) (p : Term A) (q : Term C)
      → SquareCell₌ (productMap-cong α β ▷ pair p q) (pair⁼ (α ▷ p) (β ▷ q))
          (productMap-pair f g p q) (productMap-pair f′ g′ p q)
    productMap-pair-outer-One α β p q = unconst-sides₌ (productMap-pair-outer α β p q)

    productMap-pair-inner-One : {A B C D : CAT Γ} (f : MAP A B) (g : MAP C D)
      {p p′ : Term A} {q q′ : Term C} (σ : p =₁ p′) (τ : q =₁ q′)
      → SquareCell₌ (productMap f g ◁ pair⁼ σ τ) (pair⁼ (f ◁ σ) (g ◁ τ))
          (productMap-pair f g p q) (productMap-pair f g p′ q′)
    productMap-pair-inner-One f g σ τ = unconst-sides₌ (productMap-pair-inner f g σ τ)
```
