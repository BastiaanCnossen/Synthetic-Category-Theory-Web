# Products and their universal property

The product data in Section01.Vocabulary supplies products, projections and pairing.
The product law says that taking the two coordinates of an identification is
an equivalence of animae. Its inverse assembles coordinate identifications
into an identification of functors into the product.

The calculus below constructs this identification and proves its two
projection laws, then derives the action of pairing on identifications,
precomposition of pairing, reconstruction and the elementary triple product.
It uses the composition structure without additional coherence axioms.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section02.Products where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)

module Coordinates where
  module _ {Γ : Context} where

    module _ {T : CAT Γ} where
      open Terms.InContext T using (Term)

      product-coordinates : {C D : CAT Γ} (f g : Term (C × D))
        → MAP (Equal f g) ((Equal (pr₁ ∘ f) (pr₁ ∘ g)) × (Equal (pr₂ ∘ f) (pr₂ ∘ g)))
      product-coordinates f g = pair (postWhisker pr₁) (postWhisker pr₂)

module _ {Γ : Context} where
  open Coordinates
  postulate
    product-coordinates-isEquiv : {T C D : CAT Γ} (f g : MAP T (C × D))
      → IsEquiv (product-coordinates f g)

```

## Spans and the chosen product span

These constructions need no composition of identifications. Comparisons
between span maps and their uniqueness proof are deferred.

```agda
module _ {Γ : Context} where
  record Span (C D : CAT Γ) : Set (c ⊔ m) where
    field
      apex : CAT Γ
      left : MAP apex C
      right : MAP apex D

  record SpanMap {C D : CAT Γ} (U Z : Span C D) : Set m where
    field
      functor : MAP (Span.apex U) (Span.apex Z)
      left-triangle : (Span.left Z ∘ functor) =₁ (Span.left U)
      right-triangle : (Span.right Z ∘ functor) =₁ (Span.right U)

module ProductSpans where
  module _ {Γ : Context} where

    productSpan : (C D : CAT Γ) → Span C D
    productSpan C D = record { apex = C × D ; left = pr₁ ; right = pr₂ }

    toProductSpan : {C D : CAT Γ} (U : Span C D) → SpanMap U (productSpan C D)
    toProductSpan U = record
      { functor = pair (Span.left U) (Span.right U)
      ; left-triangle = pair-β₁ (Span.left U) (Span.right U)
      ; right-triangle = pair-β₂ (Span.left U) (Span.right U)
      }
```

## Identifications into a product

For terms `x y : Term (C × D)`, take coordinate identifications
`α : (pr₁ ∘ x) ＝ (pr₁ ∘ y)` and
`β : (pr₂ ∘ x) ＝ (pr₂ ∘ y)`. We construct `pair₌ α β : x ＝ y`. Its projection laws identify its two
coordinates with `α` and `β`. Individual identifications are the case `A = One`.

The construction applies the specified inverse of `product-coordinates f g`
to `pair α β`. In the implementation, `coordinates` takes an identification
to its two coordinates, `coordinateEquivalence` supplies its inverse and
inverse laws, and `assemble` is that inverse. The paired inputs form a
family in the product of the two identification animae.

The law `coordinates-identification` states that taking coordinates of the
constructed identification recovers the paired inputs. It follows from the
specified inverse law, associativity and the unit law for functor composition.
Projecting this law gives the two individual projection laws.

```agda
module Calculus where
  module _ {Γ : Context} where
    open Constructions
    open Coordinates
    open Composition

    module _ {A X : CAT Γ} where
      open Terms.InContext X using (Term)
      open Terms.Equalities A using (_＝_)

      module ProductIdentification {C D : CAT Γ} {x y : Term (C × D)}
        (α : (pr₁ ∘ x) ＝ (pr₁ ∘ y))
        (β : (pr₂ ∘ x) ＝ (pr₂ ∘ y)) where

        private
          coordinates = product-coordinates x y
          coordinateEquivalence = product-coordinates-isEquiv x y
          assemble = IsEquiv.inverse coordinateEquivalence
          pairedInputs = pair α β

        identification : x ＝ y
        identification = assemble ∘ pairedInputs

        coordinates-identification : (coordinates ∘ identification) =₁ pairedInputs
        coordinates-identification = comp-unitˡ pairedInputs ∙
          ((IsEquiv.right-inverse-law coordinateEquivalence ▷ pairedInputs) ⁻¹ ∙
           (comp-assoc pairedInputs assemble coordinates) ⁻¹)

        β₁ : (pr₁ ◁ identification) =₁ α
        β₁ = ((pair-β₁ α β ∙ (pr₁ ◁ coordinates-identification)) ∙ comp-assoc identification coordinates pr₁)
             ∙ (pair-β₁ (postWhisker pr₁) (postWhisker pr₂) ▷ identification) ⁻¹

        β₂ : (pr₂ ◁ identification) =₁ β
        β₂ = ((pair-β₂ α β ∙ (pr₂ ◁ coordinates-identification)) ∙ comp-assoc identification coordinates pr₂)
             ∙ (pair-β₂ (postWhisker pr₁) (postWhisker pr₂) ▷ identification) ⁻¹

```

We expose the construction and its projection laws under the pairing notation.

```agda
    module _ {A X : CAT Γ} where
      open Terms.InContext X using (Term)
      open Terms.Equalities A using (_＝_)

      pair₌ : {C D : CAT Γ} {x y : Term (C × D)}
        → ((pr₁ ∘ x) ＝ (pr₁ ∘ y)) → ((pr₂ ∘ x) ＝ (pr₂ ∘ y)) → (x ＝ y)
      pair₌ = ProductIdentification.identification

      pair₌-β₁ : {C D : CAT Γ} {x y : Term (C × D)}
        (α : ((pr₁ ∘ x) ＝ (pr₁ ∘ y))) (β : ((pr₂ ∘ x) ＝ (pr₂ ∘ y)))
        → (pr₁ ◁ pair₌ α β) =₁ α
      pair₌-β₁ = ProductIdentification.β₁

      pair₌-β₂ : {C D : CAT Γ} {x y : Term (C × D)}
        (α : ((pr₁ ∘ x) ＝ (pr₁ ∘ y))) (β : ((pr₂ ∘ x) ＝ (pr₂ ∘ y)))
        → (pr₂ ◁ pair₌ α β) =₁ β
      pair₌-β₂ = ProductIdentification.β₂

```

## Pairing identifications between the factors

`pair₌` assembles identifications whose endpoints are arbitrary functors
into a product; its inputs are already coordinates of such functors. The
action of pairing is a different operation: families
`α : x ＝ x′` and `β : y ＝ y′` between terms in the individual
factors induce `pair⁼ α β : pair x y ＝ pair x′ y′`. Constant
families of the product projection laws identify the required boundaries;
`pair₌` assembles the resulting coordinate families. Pairing of individual
identifications is the case `A = One`; it needs no separate construction.

In the declarations below, `Term` uses test category `X`, while the locally
opened `＝` uses the independent identification parameter `A`. These are
transparent abbreviations; the implicit argument order and proof bodies stay
the same as in the explicit functor formulation.

```agda
    module _ {A X C D : CAT Γ} where
      open Terms.InContext X using (Term)
      open Terms.Equalities A using (_＝_)

      pair⁼ : {x x′ : Term C} {y y′ : Term D}
        → x ＝ x′ → y ＝ y′ → pair x y ＝ pair x′ y′
      pair⁼ {x = x} {x′} {y} {y′} α β = ProductIdentification.identification
        (const ((pair-β₁ x′ y′) ⁻¹) ∙ (α ∙ const (pair-β₁ x y)))
        (const ((pair-β₂ x′ y′) ⁻¹) ∙ (β ∙ const (pair-β₂ x y)))

      pair⁼-β₁ : {x x′ : Term C} {y y′ : Term D}
        (α : x ＝ x′) (β : y ＝ y′)
        → (pr₁ ◁ pair⁼ α β) =₁
            (const ((pair-β₁ x′ y′) ⁻¹) ∙ (α ∙ const (pair-β₁ x y)))
      pair⁼-β₁ {x = x} {x′} {y} {y′} α β = ProductIdentification.β₁
        (const ((pair-β₁ x′ y′) ⁻¹) ∙ (α ∙ const (pair-β₁ x y)))
        (const ((pair-β₂ x′ y′) ⁻¹) ∙ (β ∙ const (pair-β₂ x y)))

      pair⁼-β₂ : {x x′ : Term C} {y y′ : Term D}
        (α : x ＝ x′) (β : y ＝ y′)
        → (pr₂ ◁ pair⁼ α β) =₁
            (const ((pair-β₂ x′ y′) ⁻¹) ∙ (β ∙ const (pair-β₂ x y)))
      pair⁼-β₂ {x = x} {x′} {y} {y′} α β = ProductIdentification.β₂
        (const ((pair-β₁ x′ y′) ⁻¹) ∙ (α ∙ const (pair-β₁ x y)))
        (const ((pair-β₂ x′ y′) ⁻¹) ∙ (β ∙ const (pair-β₂ x y)))

```

Precomposing a pairing agrees with pairing the precomposed functors.
Again, the proof identifies the two coordinates and applies `pair₌`.

```agda
    module _ {R X : CAT Γ} where
      open Terms.InContext X using (Term)

      pair-pre : {C D : CAT Γ} (a : Term C) (b : Term D) (r : MAP R X)
        → (pair a b ∘ r) =₁ (pair (a ∘ r) (b ∘ r))
      pair-pre a b r = pair₌
        ((pair-β₁ (a ∘ r) (b ∘ r)) ⁻¹ ∙
          ((pair-β₁ a b ▷ r) ∙ (comp-assoc r (pair a b) pr₁) ⁻¹))
        ((pair-β₂ (a ∘ r) (b ∘ r)) ⁻¹ ∙
          ((pair-β₂ a b ▷ r) ∙ (comp-assoc r (pair a b) pr₂) ⁻¹))
```

## Reconstruction and projection after restriction

The product universal property reconstructs a functor from its projections.
The following projection calculations also apply after precomposition. These
are basic product calculus, used by the Section03 product equivalences.

```agda
    module _ {X : CAT Γ} where
      open Terms.InContext X using (Term)

      pair-η : {C D : CAT Γ} (z : Term (C × D))
        → (pair (pr₁ ∘ z) (pr₂ ∘ z)) =₁ z
      pair-η z = pair₌ (pair-β₁ (pr₁ ∘ z) (pr₂ ∘ z))
                              (pair-β₂ (pr₁ ∘ z) (pr₂ ∘ z))

    pair-projections : {C D : CAT Γ} → (pair pr₁ pr₂) =₁ (id (C × D))
    pair-projections = pair₌
      ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
      ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂)

    module _ {R X : CAT Γ} where
      open Terms.InContext X using (Term)

      project-pair₁ : {C D : CAT Γ}
        (x : Term C) (y : Term D) (r : MAP R X)
        → (pr₁ ∘ (pair x y ∘ r)) =₁ (x ∘ r)
      project-pair₁ x y r = (pair-β₁ x y ▷ r) ∙ (comp-assoc r (pair x y) pr₁) ⁻¹

      project-pair₂ : {C D : CAT Γ}
        (x : Term C) (y : Term D) (r : MAP R X)
        → (pr₂ ∘ (pair x y ∘ r)) =₁ (y ∘ r)
      project-pair₂ x y r = (pair-β₂ x y ▷ r) ∙ (comp-assoc r (pair x y) pr₂) ⁻¹
```

## Triples

Three functors with a common source `T` give the left-nested triple
`pair (pair γ β) α`. Its three projection computations are used to
substitute triples of identification families into laws parameterized
by a left-nested product, and by later constructions with such products.
The inputs are listed in the order of the factors.

```agda
    module _ {T : CAT Γ} where
      open Terms.InContext T using (Term)

      module Triple {A B C : CAT Γ} (γ : Term C) (β : Term B) (α : Term A) where
        triple : Term ((C × B) × A)
        triple = pair (pair γ β) α

        first : ((pr₁ ∘ pr₁) ∘ triple) =₁ γ
        first = pair-β₁ γ β ∙ ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc triple pr₁ pr₁)

        second : ((pr₂ ∘ pr₁) ∘ triple) =₁ β
        second = pair-β₂ γ β ∙ ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc triple pr₁ pr₂)

        third : (pr₂ ∘ triple) =₁ α
        third = pair-β₂ (pair γ β) α
```
