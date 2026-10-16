# Composition and its coherences

The supplied coherence families are organized alongside Section 1.2.
The primitive interface uses a single interchange law over the product of
the two identification animae.
Whiskering compatibility is derived later from these axioms. The operations `α ∙ β`, `u ◁ α`, `α ▷ k`, and `β ⋆ α` apply to families
with a common source. That source is inferred, including when it is an
identification anima or a product of them. `const` is the ordinary constant
functor. Prescribed diagrams below make the naturality and coherence boundaries explicit.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section02.Coherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions

module _ {Γ : Context} where
  postulate
    id₌ : {C D : CAT Γ} (f : MAP C D) → f =₁ f
    inv₌ : {C D : CAT Γ} {f g : MAP C D} → MAP (f ＝ g) (g ＝ f)
    comp₌ : {C D : CAT Γ} {f g h : MAP C D}
      → MAP ((g ＝ h) × (f ＝ g)) (f ＝ h)

module Composition where
  module _ {Γ : Context} where
    infixr 25 _∙_
    infixr 30 _⋆_
    infix 40 _⁻¹

    _⁻¹ : {P C D : CAT Γ} {f g : MAP C D} → MAP P (f ＝ g) → MAP P (g ＝ f)
    α ⁻¹ = inv₌ ∘ α

    _∙_ : {X C D : CAT Γ} {f g h : MAP C D}
      → MAP X (g ＝ h) → MAP X (f ＝ g) → MAP X (f ＝ h)
    β ∙ α = comp₌ ∘ pair β α

    _⋆_ : {X C D E : CAT Γ} {f f′ : MAP C D} {g g′ : MAP D E}
      → MAP X (g ＝ g′) → MAP X (f ＝ f′) → MAP X ((g ∘ f) ＝ (g′ ∘ f′))
    _⋆_ {f′ = f′} {g = g} β α = (β ▷ f′) ∙ (g ◁ α)

    hcomp : {C D E : CAT Γ} {f f′ : MAP C D} {g g′ : MAP D E}
      → MAP ((g ＝ g′) × (f ＝ f′)) ((g ∘ f) ＝ (g′ ∘ f′))
    hcomp = pr₁ ⋆ pr₂

module _ {Γ : Context} where
  postulate
    comp-unitˡ : {C D : CAT Γ} (f : MAP C D) → (id D ∘ f) =₁ f
    comp-unitʳ : {C D : CAT Γ} (f : MAP C D) → (f ∘ id C) =₁ f
    comp-assoc : {B C D E : CAT Γ} (f : MAP B C) (g : MAP C D) (h : MAP D E)
      → ((h ∘ g) ∘ f) =₁ (h ∘ (g ∘ f))

```

Identity identifications, inversion and vertical composition are supplied;
horizontal composition and its parameterized functor are definitions.
The unit and associativity operations are supplied
early because later signatures use them.

## Vertical coherence

The next five axioms follow
`post:Composition_Of_Identifications`. Each is an identification
between actual functors on the displayed parameter category.

```agda
module _ {Γ : Context} where
  open Composition
  postulate
    comp₌-unitˡ : {C D : CAT Γ} (f g : MAP C D)
      → let α = id (f ＝ g)
        in (const (id₌ g) ∙ α) =₁ α

    comp₌-unitʳ : {C D : CAT Γ} (f g : MAP C D)
      → let α = id (f ＝ g)
        in (α ∙ const (id₌ f)) =₁ α

    comp₌-assoc : {C D : CAT Γ} (f g h k : MAP C D)
      → let X = (h ＝ k) × ((g ＝ h) × (f ＝ g))
            α : MAP X (f ＝ g)
            α = pr₂ ∘ pr₂
            β : MAP X (g ＝ h)
            β = pr₁ ∘ pr₂
            γ : MAP X (h ＝ k)
            γ = pr₁
        in ((γ ∙ β) ∙ α) =₁ (γ ∙ (β ∙ α))

    comp₌-inverseˡ : {C D : CAT Γ} (f g : MAP C D)
      → let α = id (f ＝ g)
        in (α ⁻¹ ∙ α) =₁ (const (id₌ f))

    comp₌-inverseʳ : {C D : CAT Γ} (f g : MAP C D)
      → let α = id (f ＝ g)
        in (α ∙ α ⁻¹) =₁ (const (id₌ g))
```

The next axioms supply whiskering and interchange comparisons.
Identity preservation has no varying identification input. The remaining
laws are parameterized. Interchange is supplied jointly in both inputs,
using the two projections from their product as universal families.

```agda
module _ {Γ : Context} where
  open Composition
  postulate
    postWhisker-id₌ : {C D E : CAT Γ} (u : MAP D E) (f : MAP C D)
      → (u ◁ id₌ f) =₂ (id₌ (u ∘ f))

    preWhisker-id₌ : {B C D : CAT Γ} (f : MAP C D) (k : MAP B C)
      → (id₌ f ▷ k) =₂ (id₌ (f ∘ k))

    postWhisker-comp₌ : {C D E : CAT Γ} (f g h : MAP C D) (u : MAP D E)
      → let X = (g ＝ h) × (f ＝ g)
            σ : MAP X (f ＝ g)
            σ = pr₂
            τ : MAP X (g ＝ h)
            τ = pr₁
        in (u ◁ (τ ∙ σ)) =₁ ((u ◁ τ) ∙ (u ◁ σ))

    preWhisker-comp₌ : {B C D : CAT Γ} (f g h : MAP C D) (k : MAP B C)
      → let X = (g ＝ h) × (f ＝ g)
            σ : MAP X (f ＝ g)
            σ = pr₂
            τ : MAP X (g ＝ h)
            τ = pr₁
        in ((τ ∙ σ) ▷ k) =₁ ((τ ▷ k) ∙ (σ ▷ k))

    interchange : {B C D : CAT Γ} (F G : MAP C D) (h k : MAP B C)
      → let τ : MAP ((F ＝ G) × (h ＝ k)) (F ＝ G)
            τ = pr₁
            σ : MAP ((F ＝ G) × (h ＝ k)) (h ＝ k)
            σ = pr₂
        in ((τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ (τ ▷ h))

```

## Prescribed boundaries

The diagrams below have identification families as edges, all over one
common parameter category `X`, between parallel functors. They are distinct
from the squares between functors in Section03, whose edges are functors.

A square of identification families with prescribed sides commutes when
its two composite routes are identified. `SquareCell₌ top bottom left right`
is that single equation, for families given directly. `SquareBoundary`
bundles the same four edges when a named diagram is useful, and
`SquareCommutes` is the same cell for the bundled edges. Neither is a record
containing a proof, and a square with unspecified sides would be weaker.

```agda
module Boundaries where
  module _ {Γ : Context} where
    open Composition

    SquareCell₌ : {X C D : CAT Γ} {f g f′ g′ : MAP C D}
      → MAP X (f ＝ g) → MAP X (f′ ＝ g′) → MAP X (f ＝ f′) → MAP X (g ＝ g′) → Set m
    SquareCell₌ top bottom left right = (right ∙ top) =₁ (bottom ∙ left)

    record SquareBoundary {X C D : CAT Γ} (f g f′ g′ : MAP C D) : Set m where
      constructor square-boundary
      field
        top : MAP X (f ＝ g)
        bottom : MAP X (f′ ＝ g′)
        left : MAP X (f ＝ f′)
        right : MAP X (g ＝ g′)

    SquareCommutes : {X C D : CAT Γ} {f g f′ g′ : MAP C D}
      → SquareBoundary {X = X} f g f′ g′ → Set m
    SquareCommutes S = SquareCell₌ top bottom left right
      where open SquareBoundary S

    associator-naturality-square : {X B C D E : CAT Γ}
      {f f′ : MAP B C} {g g′ : MAP C D} {h h′ : MAP D E}
      (γ : MAP X (h ＝ h′)) (β : MAP X (g ＝ g′)) (α : MAP X (f ＝ f′))
      → SquareBoundary {X = X} ((h ∘ g) ∘ f) ((h′ ∘ g′) ∘ f′)
          (h ∘ (g ∘ f)) (h′ ∘ (g′ ∘ f′))
    associator-naturality-square {f = f} {f′} {g} {g′} {h} {h′} γ β α =
      square-boundary ((γ ⋆ β) ⋆ α) (γ ⋆ (β ⋆ α))
        (const (comp-assoc f g h)) (const (comp-assoc f′ g′ h′))

    unitˡ-naturality-square : {R C D : CAT Γ} {f f′ : MAP C D}
      (α : MAP R (f ＝ f′))
      → SquareBoundary {X = R} (id D ∘ f) (id D ∘ f′) f f′
    unitˡ-naturality-square {D = D} {f = f} {f′ = f′} α =
      square-boundary (const (id₌ (id D)) ⋆ α) α
        (const (comp-unitˡ f)) (const (comp-unitˡ f′))

    unitʳ-naturality-square : {R C D : CAT Γ} {f f′ : MAP C D}
      (α : MAP R (f ＝ f′))
      → SquareBoundary {X = R} (f ∘ id C) (f′ ∘ id C) f f′
    unitʳ-naturality-square {C = C} {f = f} {f′ = f′} α =
      square-boundary (α ⋆ const (id₌ (id C))) α
        (const (comp-unitʳ f)) (const (comp-unitʳ f′))

```

A triangle has three vertices `v₀`, `v₁`, `v₂`. Its source route is the
direct edge from `v₀` to `v₂`; its target route passes through `v₁`.
A pentagon has five vertices. Its source route has two edges,
`v₀ → v₁ → v₂`, and its target route has three edges,
`v₀ → v₃ → v₄ → v₂`, composed in the left-associated order
`(third ∙ second) ∙ first`. Commutativity identifies the two routes.

```agda
    record TriangleDiagram {X C D : CAT Γ} (v₀ v₁ v₂ : MAP C D) : Set m where
      constructor triangle-diagram
      field
        direct : MAP X (v₀ ＝ v₂)
        first : MAP X (v₀ ＝ v₁)
        second : MAP X (v₁ ＝ v₂)

    module _ {X C D : CAT Γ} {v₀ v₁ v₂ : MAP C D} where
      TriangleSource : TriangleDiagram {X = X} v₀ v₁ v₂ → MAP X (v₀ ＝ v₂)
      TriangleSource T = TriangleDiagram.direct T

      TriangleTarget : TriangleDiagram {X = X} v₀ v₁ v₂ → MAP X (v₀ ＝ v₂)
      TriangleTarget T = second ∙ first
        where open TriangleDiagram T

      TriangleCommutes : TriangleDiagram {X = X} v₀ v₁ v₂ → Set m
      TriangleCommutes T = TriangleSource T =₁ TriangleTarget T

    record PentagonDiagram {X C D : CAT Γ} (v₀ v₁ v₂ v₃ v₄ : MAP C D) : Set m where
      constructor pentagon-diagram
      field
        source-first : MAP X (v₀ ＝ v₁)
        source-second : MAP X (v₁ ＝ v₂)
        target-first : MAP X (v₀ ＝ v₃)
        target-second : MAP X (v₃ ＝ v₄)
        target-third : MAP X (v₄ ＝ v₂)

    module _ {X C D : CAT Γ} {v₀ v₁ v₂ v₃ v₄ : MAP C D} where
      PentagonSource : PentagonDiagram {X = X} v₀ v₁ v₂ v₃ v₄ → MAP X (v₀ ＝ v₂)
      PentagonSource P = source-second ∙ source-first
        where open PentagonDiagram P

      PentagonTarget : PentagonDiagram {X = X} v₀ v₁ v₂ v₃ v₄ → MAP X (v₀ ＝ v₂)
      PentagonTarget P = (target-third ∙ target-second) ∙ target-first
        where open PentagonDiagram P

      PentagonCommutes : PentagonDiagram {X = X} v₀ v₁ v₂ v₃ v₄ → Set m
      PentagonCommutes P = PentagonSource P =₁ PentagonTarget P

```

The next axioms supply comparisons concerning the **derived** horizontal
operation (`post:Horizontal_Composition_Is_Unital_And_Associative`). Naming the
operation does not promote it to an additional primitive.

```agda
module _ {Γ : Context} where
  open Composition
  open Boundaries
  postulate
    unitˡ-natural : {C D : CAT Γ} (f f′ : MAP C D)
      → let α = id (f ＝ f′)
        in (const (comp-unitˡ f′) ∙ (const (id₌ (id D)) ⋆ α)) =₁
          (α ∙ const (comp-unitˡ f))

    unitʳ-natural : {C D : CAT Γ} (f f′ : MAP C D)
      → let α = id (f ＝ f′)
        in (const (comp-unitʳ f′) ∙ (α ⋆ const (id₌ (id C)))) =₁
          (α ∙ const (comp-unitʳ f))

    assoc-natural : {B C D E : CAT Γ} (f f′ : MAP B C) (g g′ : MAP C D) (h h′ : MAP D E)
      → let X = ((h ＝ h′) × (g ＝ g′)) × (f ＝ f′)
            α : MAP X (f ＝ f′)
            α = pr₂
            β : MAP X (g ＝ g′)
            β = pr₂ ∘ pr₁
            γ : MAP X (h ＝ h′)
            γ = pr₁ ∘ pr₁
        in (const (comp-assoc f′ g′ h′) ∙ ((γ ⋆ β) ⋆ α)) =₁
          ((γ ⋆ (β ⋆ α)) ∙ const (comp-assoc f g h))
```

The final axioms retain the book's horizontal composites literally
(`post:Pentagon_And_Triangle_Identities`). Four composable functors generate
the associativity pentagon. Its source route reassociates twice through
`(k ∘ h) ∘ (g ∘ f)`; its target route passes through `(k ∘ (h ∘ g)) ∘ f`
and `k ∘ ((h ∘ g) ∘ f)` and is left associated. The outer edges of the
target route are horizontal composites with identity identifications, kept
literally rather than replaced by whiskerings. Two composable functors
generate the unit triangle, through `g ∘ (id D ∘ f)`. Both diagrams have
the parameter `One`, so their commutativity is an identification of
absolute identifications. These axioms compare pastings; they are not
Agda equalities.

```agda
module _ {Γ : Context} where
  open Composition
  open Boundaries

  associativityPentagon : {A B C D E : CAT Γ} (f : MAP A B) (g : MAP B C)
    (h : MAP C D) (k : MAP D E)
    → PentagonDiagram {X = One}
        (((k ∘ h) ∘ g) ∘ f) ((k ∘ h) ∘ (g ∘ f)) (k ∘ (h ∘ (g ∘ f)))
        ((k ∘ (h ∘ g)) ∘ f) (k ∘ ((h ∘ g) ∘ f))
  associativityPentagon f g h k = pentagon-diagram
    (comp-assoc f g (k ∘ h)) (comp-assoc (g ∘ f) h k)
    (comp-assoc g h k ⋆ id₌ f) (comp-assoc f (h ∘ g) k) (id₌ k ⋆ comp-assoc f g h)

  unitTriangle : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E)
    → TriangleDiagram {X = One} ((g ∘ id D) ∘ f) (g ∘ (id D ∘ f)) (g ∘ f)
  unitTriangle {D = D} f g = triangle-diagram
    (comp-unitʳ g ⋆ id₌ f) (comp-assoc f (id D) g) (id₌ g ⋆ comp-unitˡ f)

  postulate
    comp-pentagon : {A B C D E : CAT Γ} (f : MAP A B) (g : MAP B C)
      (h : MAP C D) (k : MAP D E)
      → PentagonCommutes (associativityPentagon f g h k)

    comp-triangle : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E)
      → TriangleCommutes (unitTriangle f g)
```

Unfolding the definitions, `comp-pentagon f g h k` is the original equation

    comp-assoc (g ∘ f) h k ∙ comp-assoc f g (k ∘ h) =₂
      ((id₌ k ⋆ comp-assoc f g h) ∙ comp-assoc f (h ∘ g) k) ∙ (comp-assoc g h k ⋆ id₌ f)

and `comp-triangle f g` is
`(comp-unitʳ g ⋆ id₌ f) =₂ ((id₌ g ⋆ comp-unitˡ f) ∙ comp-assoc f (id D) g)`.
