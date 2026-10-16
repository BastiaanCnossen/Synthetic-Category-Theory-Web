# Pairing of identifications

Section02.Products constructs `pair⁼ α β` for identification families
`α : MAP A (f ＝ f′)` and `β : MAP A (g ＝ g′)` with a common parameter `A`;
individual identifications are the case `A = One`. This module proves its
basic calculus.

The organizing fact is that an identification into a product is determined
by its two projections. In the form used here: an identification family
`ε : MAP A (h ＝ h′)` into `C × D` lies over `α` and `β` when its projections
form squares with `α` and `β` along given projection triangles of `h` and
`h′`, and two families lying over the same `α` and `β` are identified
(`pair₌-unique`). The projection triangles of `pair⁼ α β` say that it lies
over `α` and `β`. Congruence, composition, identity and naturality of pairing
then follow by exhibiting both sides as lying over the same pair. Restriction
of the parameter, constant families and the functor `pair⁼-functor` on
identification animae follow from the construction.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.Pairing where

import SCT.VolumeI.Chapter01.Section02.Naturality as N

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Coordinates
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-reflect)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (lies-over-comp; lies-over-id; lies-over-id-One)
```

The pairing input operations have external pairs of functors as inputs and
external pairs of identification families as changes.

```agda
module _ {Γ : Context} where
  pairing-input₁ : (X C D : CAT Γ)
    → N.Operation (N.Inputs₂ (MAP X C) (MAP X D))
        (N.PairChange (N.HomChange X C) (N.HomChange X D)) X C
  pairing-input₁ X C D = N.PairInput₁ X C X D

  pairing-input₂ : (X C D : CAT Γ)
    → N.Operation (N.Inputs₂ (MAP X C) (MAP X D))
        (N.PairChange (N.HomChange X C) (N.HomChange X D)) X D
  pairing-input₂ X C D = N.PairInput₂ X C X D

  pairing-operation : (X C D : CAT Γ)
    → N.Operation (N.Inputs₂ (MAP X C) (MAP X D))
        (N.PairChange (N.HomChange X C) (N.HomChange X D)) X (C × D)
  pairing-operation X C D = N.Pair (pairing-input₁ X C D) (pairing-input₂ X C D)
```

## Identifications into a product

Taking the two coordinates of an identification is an equivalence, so it
reflects identifications. Cancelling the target triangles then shows that
an identification lying over a given pair is unique.

```agda
module _ {Γ : Context} where
  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair₌-extensionality : {C D : CAT Γ} {x y : Term (C × D)}
      {α β : x ＝ y}
      → (pr₁ ◁ α) =₁ (pr₁ ◁ β) → (pr₂ ◁ α) =₁ (pr₂ ◁ β) → α =₁ β
    pair₌-extensionality {x = x} {y} {α} {β} p q =
      equiv-reflect (product-coordinates-isEquiv x y) α β
        ((pair-pre (postWhisker pr₁) (postWhisker pr₂) β) ⁻¹ ∙
          (pair⁼ p q ∙ pair-pre (postWhisker pr₁) (postWhisker pr₂) α))

    pair₌-unique : {C D : CAT Γ} {z z′ : Term (C × D)}
      {x x′ : Term C} {y y′ : Term D}
      {b₁ : ((pr₁ ∘ z) ＝ x)} {b₁′ : ((pr₁ ∘ z′) ＝ x′)}
      {b₂ : ((pr₂ ∘ z) ＝ y)} {b₂′ : ((pr₂ ∘ z′) ＝ y′)}
      {α : x ＝ x′} {β : y ＝ y′}
      {ε ε′ : z ＝ z′}
      → SquareCell₌ (pr₁ ◁ ε) α b₁ b₁′
      → SquareCell₌ (pr₂ ◁ ε) β b₂ b₂′
      → SquareCell₌ (pr₁ ◁ ε′) α b₁ b₁′
      → SquareCell₌ (pr₂ ◁ ε′) β b₂ b₂′
      → ε =₁ ε′
    pair₌-unique {b₁′ = b₁′} {b₂′ = b₂′} first second first′ second′ =
      pair₌-extensionality
        (cancel-left b₁′ (first′ ⁻¹ ∙ first))
        (cancel-left b₂′ (second′ ⁻¹ ∙ second))
```

## Projection triangles

`pair⁼ α β` lies over `α` and `β` along the product projection laws.
`pair-pre f g r` lies over the identity: its projections are the restricted
projection laws `project-pair₁` and `project-pair₂`.

```agda
module _ {Γ : Context} where
  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair⁼-triangle₁ : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x ＝ x′) (β : y ＝ y′)
      → N.NaturalityAt (N.Post pr₁ (pairing-operation X C D)) (pairing-input₁ X C D)
          (λ q → pair-β₁ (N.Inputs₂.first q) (N.Inputs₂.second q)) (N.inputs₂ α β)
    pair⁼-triangle₁  {x = x} {x′} {y} {y′} α β =
      comp-inv-left (const (pair-β₁ x′ y′)) (α ∙ const (pair-β₁ x y)) ∙
        comp₌-cong (id₌ (const (pair-β₁ x′ y′)))
          (comp₌-cong (const-inv {X = A} (pair-β₁ x′ y′)) (id₌ (α ∙ const (pair-β₁ x y))) ∙
            pair⁼-β₁ α β)

    pair⁼-triangle₂ : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x ＝ x′) (β : y ＝ y′)
      → N.NaturalityAt (N.Post pr₂ (pairing-operation X C D)) (pairing-input₂ X C D)
          (λ q → pair-β₂ (N.Inputs₂.first q) (N.Inputs₂.second q)) (N.inputs₂ α β)
    pair⁼-triangle₂  {x = x} {x′} {y} {y′} α β =
      comp-inv-left (const (pair-β₂ x′ y′)) (β ∙ const (pair-β₂ x y)) ∙
        comp₌-cong (id₌ (const (pair-β₂ x′ y′)))
          (comp₌-cong (const-inv {X = A} (pair-β₂ x′ y′)) (id₌ (β ∙ const (pair-β₂ x y))) ∙
            pair⁼-β₂ α β)

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair⁼-triangle₁-One : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x =₁ x′) (β : y =₁ y′)
      → SquareCell₌ (pr₁ ◁ pair⁼ α β) α (pair-β₁ x y) (pair-β₁ x′ y′)
    pair⁼-triangle₁-One α β = unconst-sides₌ (pair⁼-triangle₁ α β)

    pair⁼-triangle₂-One : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x =₁ x′) (β : y =₁ y′)
      → SquareCell₌ (pr₂ ◁ pair⁼ α β) β (pair-β₂ x y) (pair-β₂ x′ y′)
    pair⁼-triangle₂-One α β = unconst-sides₌ (pair⁼-triangle₂ α β)

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-pre-triangle₁ : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      → (pair-β₁ (x ∘ r) (y ∘ r) ∙ (pr₁ ◁ pair-pre x y r)) =₂ project-pair₁ x y r
    pair-pre-triangle₁ x y r =
      comp-inv-left (pair-β₁ (x ∘ r) (y ∘ r)) (project-pair₁ x y r) ∙
        comp₌-cong (id₌ (pair-β₁ (x ∘ r) (y ∘ r)))
          (pair₌-β₁ ((pair-β₁ (x ∘ r) (y ∘ r)) ⁻¹ ∙ project-pair₁ x y r)
            ((pair-β₂ (x ∘ r) (y ∘ r)) ⁻¹ ∙ project-pair₂ x y r))

    pair-pre-triangle₂ : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      → (pair-β₂ (x ∘ r) (y ∘ r) ∙ (pr₂ ◁ pair-pre x y r)) =₂ project-pair₂ x y r
    pair-pre-triangle₂ x y r =
      comp-inv-left (pair-β₂ (x ∘ r) (y ∘ r)) (project-pair₂ x y r) ∙
        comp₌-cong (id₌ (pair-β₂ (x ∘ r) (y ∘ r)))
          (pair₌-β₂ ((pair-β₁ (x ∘ r) (y ∘ r)) ⁻¹ ∙ project-pair₁ x y r)
            ((pair-β₂ (x ∘ r) (y ∘ r)) ⁻¹ ∙ project-pair₂ x y r))
```

## Functoriality

Both sides of each law lie over the same pair of identifications.

```agda
module _ {Γ : Context} where
  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair⁼-cong : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      {α α′ : x ＝ x′} {β β′ : y ＝ y′}
      → α =₁ α′ → β =₁ β′ → pair⁼ α β =₁ pair⁼ α′ β′
    pair⁼-cong {α = α} {α′} {β} {β′} p q = pair₌-unique
      (pair⁼-triangle₁ α β) (pair⁼-triangle₂ α β)
      (replace-edges₌ (id₌ (pr₁ ◁ pair⁼ α′ β′)) (p ⁻¹) (pair⁼-triangle₁ α′ β′))
      (replace-edges₌ (id₌ (pr₂ ◁ pair⁼ α′ β′)) (q ⁻¹) (pair⁼-triangle₂ α′ β′))

    pair⁼-comp : {C D : CAT Γ} {x₀ x₁ x₂ : Term C} {y₀ y₁ y₂ : Term D}
      (α₂ : x₁ ＝ x₂) (α₁ : x₀ ＝ x₁)
      (β₂ : y₁ ＝ y₂) (β₁ : y₀ ＝ y₁)
      → pair⁼ (α₂ ∙ α₁) (β₂ ∙ β₁) =₁ (pair⁼ α₂ β₂ ∙ pair⁼ α₁ β₁)
    pair⁼-comp α₂ α₁ β₂ β₁ = pair₌-unique
      (pair⁼-triangle₁ (α₂ ∙ α₁) (β₂ ∙ β₁)) (pair⁼-triangle₂ (α₂ ∙ α₁) (β₂ ∙ β₁))
      (lies-over-comp pr₁ (pair⁼-triangle₁ α₁ β₁) (pair⁼-triangle₁ α₂ β₂))
      (lies-over-comp pr₂ (pair⁼-triangle₂ α₁ β₁) (pair⁼-triangle₂ α₂ β₂))

  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair⁼-id : {C D : CAT Γ} (x : Term C) (y : Term D)
      → pair⁼ (const {P = A} (id₌ x)) (const (id₌ y)) =₁ const (id₌ (pair x y))
    pair⁼-id x y = pair₌-unique
      (pair⁼-triangle₁ (const (id₌ x)) (const (id₌ y)))
      (pair⁼-triangle₂ (const (id₌ x)) (const (id₌ y)))
      (lies-over-id pr₁ (pair-β₁ x y)) (lies-over-id pr₂ (pair-β₂ x y))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair⁼-id-One : {C D : CAT Γ} (x : Term C) (y : Term D)
      → pair⁼ (id₌ x) (id₌ y) =₂ id₌ (pair x y)
    pair⁼-id-One x y = pair₌-unique
      (pair⁼-triangle₁-One (id₌ x) (id₌ y)) (pair⁼-triangle₂-One (id₌ x) (id₌ y))
      (lies-over-id-One pr₁ (pair-β₁ x y)) (lies-over-id-One pr₂ (pair-β₂ x y))
```

Pairing carries a pair of squares to a square. With a fixed identity first
coordinate, pairing preserves composition in the second coordinate.

```agda
  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair⁼-square : {C D : CAT Γ}
      {a a′ b b′ : Term C} {d d′ e e′ : Term D}
      {t₁ : a ＝ b} {b₁ : a′ ＝ b′}
      {l₁ : a ＝ a′} {r₁ : b ＝ b′}
      {t₂ : d ＝ e} {b₂ : d′ ＝ e′}
      {l₂ : d ＝ d′} {r₂ : e ＝ e′}
      → SquareCell₌ t₁ b₁ l₁ r₁ → SquareCell₌ t₂ b₂ l₂ r₂
      → SquareCell₌ (pair⁼ t₁ t₂) (pair⁼ b₁ b₂) (pair⁼ l₁ l₂) (pair⁼ r₁ r₂)
    pair⁼-square {t₁ = t₁} {b₁} {l₁} {r₁} {t₂} {b₂} {l₂} {r₂} p q =
      pair⁼-comp b₁ l₁ b₂ l₂ ∙ (pair⁼-cong p q ∙ (pair⁼-comp r₁ t₁ r₂ t₂) ⁻¹)

    pair⁼-fixed-first-comp : {C D : CAT Γ} (x : Term C) {y z w : Term D}
      (β : z ＝ w) (α : y ＝ z)
      → pair⁼ (const (id₌ x)) (β ∙ α) =₁ (pair⁼ (const (id₌ x)) β ∙ pair⁼ (const (id₌ x)) α)
    pair⁼-fixed-first-comp x β α = pair⁼-comp (const (id₌ x)) (const (id₌ x)) β α ∙
      pair⁼-cong ((comp₌-unitˡ (const (id₌ x))) ⁻¹) (id₌ (β ∙ α))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair⁼-fixed-first-comp-One : {C D : CAT Γ} (x : Term C) {y z w : Term D}
      (β : z =₁ w) (α : y =₁ z)
      → pair⁼ (id₌ x) (β ∙ α) =₂ (pair⁼ (id₌ x) β ∙ pair⁼ (id₌ x) α)
    pair⁼-fixed-first-comp-One x β α =
      comp₌-cong (pair⁼-cong (const-One (id₌ x)) (id₌ β))
        (pair⁼-cong (const-One (id₌ x)) (id₌ α)) ∙
        (pair⁼-fixed-first-comp x β α ∙
          (pair⁼-cong (const-One (id₌ x)) (id₌ (β ∙ α))) ⁻¹)
```

## Change of parameter

Restricting a pairing along `r` pairs the restricted families. It is computed
from the construction: the coordinate families are restricted by the
evaluation lemmas for composites and constants. Over `A`, the constant
families of a pair of identifications pair to the constant family of their
pairing. The universal pairing is the functor `pair⁼-functor` on the product of
the identification animae; it evaluates at a pair of families to their
pairing.

```agda
module _ {Γ : Context} where
  module _ {A B X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair⁼-pre : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x ＝ x′) (β : y ＝ y′) (r : MAP B A)
      → (pair⁼ α β ∘ r) =₁ pair⁼ (α ∘ r) (β ∘ r)
    pair⁼-pre {x = x} {x′} {y} {y′} α β r =
      let first = const ((pair-β₁ x′ y′) ⁻¹) ∙ (α ∙ const (pair-β₁ x y))
          second = const ((pair-β₂ x′ y′) ⁻¹) ∙ (β ∙ const (pair-β₂ x y))
          first-pre = comp₌-evaluate-One (const ((pair-β₁ x′ y′) ⁻¹))
            (α ∙ const (pair-β₁ x y)) r (const-pre ((pair-β₁ x′ y′) ⁻¹) r)
            (comp₌-evaluate-One α (const (pair-β₁ x y)) r (id₌ (α ∘ r))
              (const-pre (pair-β₁ x y) r))
          second-pre = comp₌-evaluate-One (const ((pair-β₂ x′ y′) ⁻¹))
            (β ∙ const (pair-β₂ x y)) r (const-pre ((pair-β₂ x′ y′) ⁻¹) r)
            (comp₌-evaluate-One β (const (pair-β₂ x y)) r (id₌ (β ∘ r))
              (const-pre (pair-β₂ x y) r))
          assemble = IsEquiv.inverse (product-coordinates-isEquiv (pair x y) (pair x′ y′))
      in (assemble ◁ (pair⁼ first-pre second-pre ∙ pair-pre first second r)) ∙
        comp-assoc r (pair first second) assemble

  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair⁼-constant : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x =₁ x′) (β : y =₁ y′)
      → pair⁼ (const {P = A} α) (const β) =₁ const (pair⁼ α β)
    pair⁼-constant  α β = (pair⁼-pre α β (terminate A)) ⁻¹

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair⁼-functor : {C D : CAT Γ} (x x′ : Term C) (y y′ : Term D)
      → MAP ((Equal x x′) × (Equal y y′)) (Equal (pair x y) (pair x′ y′))
    pair⁼-functor x x′ y y′ = pair⁼ pr₁ pr₂

  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair⁼-evaluate : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x ＝ x′) (β : y ＝ y′)
      → (pair⁼-functor x x′ y y′ ∘ pair α β) =₁ pair⁼ α β
    pair⁼-evaluate α β =
      pair⁼-cong (pair-β₁ α β) (pair-β₂ α β) ∙ pair⁼-pre pr₁ pr₂ (pair α β)
```

## Naturality of the specified projection identifications

The adapters evaluate the existing chosen cancellation proofs on the external
pair of input changes. They do not replace pairing by a universal evaluation.

```agda
module _ {Γ : Context} where
  pair-β₁-naturality : (X C D : CAT Γ)
    → N.Naturality (N.Post pr₁ (pairing-operation X C D)) (pairing-input₁ X C D)
        (λ q → pair-β₁ (N.Inputs₂.first q) (N.Inputs₂.second q))
  pair-β₁-naturality X C D (N.inputs₂ α β) = pair⁼-triangle₁ α β

  pair-β₂-naturality : (X C D : CAT Γ)
    → N.Naturality (N.Post pr₂ (pairing-operation X C D)) (pairing-input₂ X C D)
        (λ q → pair-β₂ (N.Inputs₂.first q) (N.Inputs₂.second q))
  pair-β₂-naturality X C D (N.inputs₂ α β) = pair⁼-triangle₂ α β
```
