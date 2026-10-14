# Pairing with the first projection

The product `P × C` with its first projection is a category over `P`,
`product-over P C`. A functor `f : P × C → D` determines the functor
`pair-pr₁ f = pair pr₁ f : P × C → P × D` over `P`, whose triangle is the
projection law `pair-pr₁-β₁ f`. This module specializes the calculus of
identifications over a base (Identifications.OverBase) to these
functors: the action of `pair-pr₁` on identifications is an identification
over `P`, the composite of `pair-pr₁ g` and `pair-pr₁ f` over `P` is
identified over `P` with `pair-pr₁ (g ∘ pair-pr₁ f)` by `pair-pr₁-compose`,
which is natural, and the identity functor over `P` is `pair-pr₁ pr₂` by
`pair-projections`. Changing the parameter along `σ : Q → P` is the functor
`change-parameter σ` over the map `σ`. Each relative statement has a
`-compatible` form for the specified underlying identification.

The action on identifications and its composition and over-base laws are
family statements. The `-One` forms preserve the specified expressions used
in the remaining fixed-diagram computations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
  using (CategoryOverBase; category-over; FunctorOverBase; functor-over; id-over; comp-over;
    FunctorOverMap)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares using (replace-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares using (combine-pair)
```

## Functors over the first factor

```agda
module _ {Γ : Context} where
  product-over : (P C : CAT Γ) → CategoryOverBase P
  product-over P C = category-over (P × C) pr₁

  module OverFirstFactor (P : CAT Γ) where

    pair-pr₁ : {C D : CAT Γ} → MAP (P × C) D → MAP (P × C) (P × D)
    pair-pr₁ f = pair pr₁ f

    pair-pr₁-β₁ : {C D : CAT Γ} (f : MAP (P × C) D) → (pr₁ ∘ pair-pr₁ f) =₁ pr₁
    pair-pr₁-β₁ f = pair-β₁ pr₁ f

    pair-pr₁-β₂ : {C D : CAT Γ} (f : MAP (P × C) D) → (pr₂ ∘ pair-pr₁ f) =₁ f
    pair-pr₁-β₂ f = pair-β₂ pr₁ f

    pair-pr₁-over : {C D : CAT Γ} (f : MAP (P × C) D)
      → FunctorOverBase (product-over P C) (product-over P D)
    pair-pr₁-over f = functor-over (pair-pr₁ f) (pair-pr₁-β₁ f)

    module _ {A : CAT Γ} where
      open Terms.Equalities A using (_＝_)

      pair-pr₁-cong : {C D : CAT Γ} {f g : MAP (P × C) D}
        → f ＝ g → pair-pr₁ f ＝ pair-pr₁ g
      pair-pr₁-cong α = pair⁼ (const (id₌ pr₁)) α

      pair-pr₁-cong-comp : {C D : CAT Γ} {f g h : MAP (P × C) D}
        (β : g ＝ h) (α : f ＝ g)
        → pair-pr₁-cong (β ∙ α) =₁ (pair-pr₁-cong β ∙ pair-pr₁-cong α)
      pair-pr₁-cong-comp β α = pair⁼-fixed-first-comp pr₁ β α

      pair-pr₁-cong-over : {C D : CAT Γ} {f g : MAP (P × C) D} (α : f ＝ g)
        → IsIdentificationOver (pair-pr₁-over f) (pair-pr₁-over g) (pair-pr₁-cong α)
      pair-pr₁-cong-over α = pair⁼-triangle₁ (const (id₌ pr₁)) α

    pair-pr₁-cong-One : {C D : CAT Γ} {f g : MAP (P × C) D}
      → f =₁ g → pair-pr₁ f =₁ pair-pr₁ g
    pair-pr₁-cong-One α = pair⁼ (id₌ pr₁) α

    pair-pr₁-cong-comp-One : {C D : CAT Γ} {f g h : MAP (P × C) D}
      (β : g =₁ h) (α : f =₁ g)
      → pair-pr₁-cong-One (β ∙ α) =₂ (pair-pr₁-cong-One β ∙ pair-pr₁-cong-One α)
    pair-pr₁-cong-comp-One β α = pair⁼-fixed-first-comp-One pr₁ β α

    pair-pr₁-cong-compatible-One : {C D : CAT Γ} {f g : MAP (P × C) D} (α : f =₁ g)
      → CompatibleOver pr₁ (pair-pr₁-β₁ f) (pair-pr₁-β₁ g) (pair-pr₁-cong-One α)
    pair-pr₁-cong-compatible-One {f = f} α = comp₌-unitˡ-One (pair-pr₁-β₁ f) ∙
      pair⁼-triangle₁-One (id₌ pr₁) α

    pair-pr₁-cong-over-One : {C D : CAT Γ} {f g : MAP (P × C) D} (α : f =₁ g)
      → IsIdentificationOver (pair-pr₁-over f) (pair-pr₁-over g) (pair-pr₁-cong-One α)
    pair-pr₁-cong-over-One α = compatible-to-over (pair-pr₁-cong-compatible-One α)

    pair-pr₁-id : (C : CAT Γ) → pair-pr₁ {C} pr₂ =₁ id (P × C)
    pair-pr₁-id C = pair-projections

    pair-pr₁-id-over : (C : CAT Γ)
      → IsIdentificationOver (pair-pr₁-over {C} pr₂) (id-over (product-over P C)) (pair-pr₁-id C)
    pair-pr₁-id-over C = compatible-to-over pair-projections-triangle₁

```

Restricting an identification `pair-pr₁ z = id`, built from `u : z = pr₂`,
along a pairing `pair f g` is computed by the paired evaluation.

```agda
    pair-pr₁-id-pre : {X C : CAT Γ} (f : MAP X P) (g : MAP X C)
      {z : MAP (P × C) C} (u : z =₁ pr₂)
      → (comp-unitˡ (pair f g) ∙ ((pair-projections ∙ pair⁼ (id₌ pr₁) u) ▷ pair f g)) =₂
          (pair⁼ (pair-β₁ f g) (pair-β₂ f g ∙ (u ▷ pair f g)) ∙ pair-pre pr₁ z (pair f g))
    pair-pr₁-id-pre f g {z} u =
      let s = pair f g
          η = pair-projections
          r = pair⁼ (id₌ pr₁) u
          first = pair-β₁ f g
          second = pair-β₂ f g
          out = pair⁼ first second
          pre = pair-pre pr₁ pr₂ s
          normalize = comp₌-unitʳ-One first ∙ comp₌-cong (id₌ first) (preWhisker-id₌ pr₁ s)
      in comp₌-cong (pair⁼-cong normalize (id₌ (second ∙ (u ▷ s)))) (id₌ (pair-pre pr₁ z s)) ∙
        (combine-pair first second (id₌ pr₁ ▷ s) (u ▷ s) (pair-pre pr₁ z s) ∙
        (comp₌-cong (id₌ out) (pair-pre-natural-inputs-One (id₌ pr₁) u s) ∙
        (comp₌-assoc out pre (r ▷ s) ∙
        (comp₌-cong (pair-projections-pre f g) (id₌ (r ▷ s)) ∙
        ((comp₌-assoc (comp-unitˡ s) (η ▷ s) (r ▷ s)) ⁻¹ ∙
          comp₌-cong (id₌ (comp-unitˡ s)) (preWhisker-comp₌ η r s))))))
```

## Composition

`pair-pr₁ g ∘ pair-pr₁ f` is `pair-pr₁ (g ∘ pair-pr₁ f)`: the paired
evaluation of the first projection law of `f` and the identity. Its second
projection is the restricted second projection law, it lies over the base,
and it is natural in `f` and `g`.

```agda
    pair-pr₁-compose : {C D E : CAT Γ} (g : MAP (P × D) E) (f : MAP (P × C) D)
      → (pair-pr₁ g ∘ pair-pr₁ f) =₁ pair-pr₁ (g ∘ pair-pr₁ f)
    pair-pr₁-compose g f = pair⁼ (pair-pr₁-β₁ f) (id₌ (g ∘ pair-pr₁ f)) ∙
      pair-pre pr₁ g (pair-pr₁ f)

    composite-β₂ : {C D E : CAT Γ} (g : MAP (P × D) E) (f : MAP (P × C) D)
      → (pr₂ ∘ (pair-pr₁ g ∘ pair-pr₁ f)) =₁ (g ∘ pair-pr₁ f)
    composite-β₂ g f = restrict-triangle pr₂ (pair-pr₁ g) (pair-pr₁-β₂ g) (pair-pr₁ f)

    abstract
      pair-pr₁-compose-β₂ : {C D E : CAT Γ} (g : MAP (P × D) E) (f : MAP (P × C) D)
        → (pair-pr₁-β₂ (g ∘ pair-pr₁ f) ∙ (pr₂ ◁ pair-pr₁-compose g f)) =₂ composite-β₂ g f
      pair-pr₁-compose-β₂ g f = comp₌-unitˡ-One (composite-β₂ g f) ∙
        pair-evaluation-over₂-One pr₁ g (pair-pr₁ f) (pair-pr₁-β₁ f) (id₌ (g ∘ pair-pr₁ f))

    pair-pr₁-compose-compatible : {C D E : CAT Γ} (g : MAP (P × D) E) (f : MAP (P × C) D)
      → CompatibleOver pr₁
          (compose-triangle pr₁ (pair-pr₁ g) (pair-pr₁-β₁ g) (pair-pr₁ f) (pair-pr₁-β₁ f))
          (pair-pr₁-β₁ (g ∘ pair-pr₁ f)) (pair-pr₁-compose g f)
    pair-pr₁-compose-compatible g f = pair-evaluation-over₁-One pr₁ g (pair-pr₁ f)
      (pair-pr₁-β₁ f) (id₌ (g ∘ pair-pr₁ f))

    pair-pr₁-compose-over : {C D E : CAT Γ} (g : MAP (P × D) E) (f : MAP (P × C) D)
      → IsIdentificationOver (comp-over (pair-pr₁-over g) (pair-pr₁-over f))
          (pair-pr₁-over (g ∘ pair-pr₁ f)) (pair-pr₁-compose g f)
    pair-pr₁-compose-over g f = compatible-to-over (pair-pr₁-compose-compatible g f)

    module _ {A : CAT Γ} where
      open Terms.Equalities A using (_＝_)

      pair-pr₁-compose-natural : {C D E : CAT Γ}
        {g g′ : MAP (P × D) E} {f f′ : MAP (P × C) D}
        (α : g ＝ g′) (β : f ＝ f′)
        → (const (pair-pr₁-compose g′ f′) ∙ (pair-pr₁-cong α ⋆ pair-pr₁-cong β)) =₁
            (pair-pr₁-cong (α ⋆ pair-pr₁-cong β) ∙ const (pair-pr₁-compose g f))
      pair-pr₁-compose-natural {g = g} {g′} {f} {f′} α β =
        let δ = pair-pr₁-cong β
            changed = α ⋆ δ
            before = const (pair-pre pr₁ g (pair-pr₁ f))
            after = const (pair-pre pr₁ g′ (pair-pr₁ f′))
            normalize-before = pair⁼ (const (pair-pr₁-β₁ f)) (const (id₌ (g ∘ pair-pr₁ f)))
            normalize-after = pair⁼ (const (pair-pr₁-β₁ f′)) (const (id₌ (g′ ∘ pair-pr₁ f′)))
            horizontal-unit = hcomp-id-outer pr₁ δ
            first = comp₌-unitˡ (const (pair-pr₁-β₁ f)) ∙
              (pair⁼-triangle₁ (const (id₌ pr₁)) β ∙
                comp₌-cong (id₌ (const (pair-pr₁-β₁ f′))) horizontal-unit)
            left-normal = comp₌-cong
              (pair⁼-cong first (comp₌-unitˡ changed) ∙
                (pair⁼-comp (const (pair-pr₁-β₁ f′)) (const (id₌ pr₁) ⋆ δ)
                  (const (id₌ (g′ ∘ pair-pr₁ f′))) changed) ⁻¹) (id₌ before) ∙
              ((comp₌-assoc normalize-after (pair⁼ (const (id₌ pr₁) ⋆ δ) changed) before) ⁻¹ ∙
              (comp₌-cong (id₌ normalize-after) (pair-pre-natural (const (id₌ pr₁)) α δ) ∙
                comp₌-assoc normalize-after after (pair-pr₁-cong α ⋆ δ)))
            right-normal = comp₌-cong
              (pair⁼-cong (comp₌-unitˡ (const (pair-pr₁-β₁ f))) (comp₌-unitʳ changed) ∙
                (pair⁼-comp (const (id₌ pr₁)) (const (pair-pr₁-β₁ f))
                  changed (const (id₌ (g ∘ pair-pr₁ f)))) ⁻¹) (id₌ before) ∙
              (comp₌-assoc (pair-pr₁-cong changed) normalize-before before) ⁻¹
            normalize g f = const-comp (pair⁼ (pair-pr₁-β₁ f) (id₌ (g ∘ pair-pr₁ f)))
                (pair-pre pr₁ g (pair-pr₁ f)) ∙
              comp₌-cong (pair⁼-constant (pair-pr₁-β₁ f) (id₌ (g ∘ pair-pr₁ f)))
                (id₌ (const (pair-pre pr₁ g (pair-pr₁ f))))
        in replace-sides₌ (normalize g f) (normalize g′ f′) (right-normal ⁻¹ ∙ left-normal)
```

## Changing the parameter

Along `σ : Q → P`, `productMap σ (id D)` is a functor over the map `σ`, from
`product-over Q D` to `product-over P D`. It changes only the parameter, so
an equation after postcomposing with it gives the equation of second
projections.

```agda
module _ {Γ : Context} where
  change-parameter : {Q P D : CAT Γ} (σ : MAP Q P)
    → FunctorOverMap σ (product-over Q D) (product-over P D)
  change-parameter {D = D} σ = functor-over (productMap σ (id D)) (pair-β₁ (σ ∘ pr₁) (id D ∘ pr₂))

  second-projection : {Q P D : CAT Γ} (σ : MAP Q P)
    → (pr₂ ∘ productMap σ (id D)) =₁ pr₂ {C = Q} {D = D}
  second-projection {D = D} σ = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id D ∘ pr₂)

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    reflect-second : {Q P X D : CAT Γ} (σ : MAP Q P) {f g : MAP X (Q × D)}
      {α β : f ＝ g}
      → (productMap σ (id D) ◁ α) =₁ (productMap σ (id D) ◁ β)
      → (pr₂ ◁ α) =₁ (pr₂ ◁ β)
    reflect-second {D = D} σ p = postWhisker-change-transfer (second-projection σ)
      (postWhisker-comp-transfer (productMap σ (id D)) pr₂ (postWhisker pr₂ ◁ p))
```
