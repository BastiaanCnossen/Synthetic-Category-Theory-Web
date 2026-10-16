# Pairing and restriction

`pair-pre f g r : pair f g ∘ r = pair (f ∘ r) (g ∘ r)` lies over the
identity: its projections are the restricted projection laws
`project-pair₁` and `project-pair₂`. Consequently the paired evaluation
`pair⁼ α β ∙ pair-pre f g r` lies over `α` and `β`. With the uniqueness of
identifications lying over a given pair (`pair₌-unique`), this single fact
gives the naturality of `pair-pre` in the paired functors and in the
restricting functor, its compatibility with the right unitor and with
iterated restriction, the naturality of paired evaluation, and the
restriction of a left-nested triple.

Naturality statements are `SquareCell₌` squares for identification families,
with the constant families of `pair-pre` as sides. The instances at `One`
(suffix `-One`) have `pair-pre` itself as sides.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction where

import SCT.VolumeI.Chapter01.Section02.Naturality as N

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌;
    module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
import SCT.VolumeI.Chapter01.Section02.Whiskering as Whiskering
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
```

The joint input is an external triple of two terms and a restriction functor.
Its changes are three families over a common arbitrary parameter.

```agda
module _ {Γ : Context} where
  RestrictionInputs : (R X C D : CAT Γ) → Set m
  RestrictionInputs R X C D = N.Inputs₃ (MAP X C) (MAP X D) (MAP R X)

  RestrictionChange : (R X C D : CAT Γ) → CAT Γ
    → RestrictionInputs R X C D → RestrictionInputs R X C D → Set m
  RestrictionChange R X C D = N.TripleChange (N.HomChange X C) (N.HomChange X D) (N.HomChange R X)

  RestrictionBefore : (R X C D : CAT Γ)
    → N.Operation (RestrictionInputs R X C D) (RestrictionChange R X C D) R (C × D)
  RestrictionBefore R X C D = N.Compose
    (N.Pair (N.TripleInput₁ X C X D R X) (N.TripleInput₂ X C X D R X))
    (N.TripleInput₃ X C X D R X)

  RestrictionAfter : (R X C D : CAT Γ)
    → N.Operation (RestrictionInputs R X C D) (RestrictionChange R X C D) R (C × D)
  RestrictionAfter R X C D = N.Pair
    (N.Compose (N.TripleInput₁ X C X D R X) (N.TripleInput₃ X C X D R X))
    (N.Compose (N.TripleInput₂ X C X D R X) (N.TripleInput₃ X C X D R X))
```

## Restriction lies over the identity

```agda
module _ {Γ : Context} where
  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-pre-over₁ : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      → SquareCell₌ (pr₁ ◁ const {P = A} (pair-pre x y r)) (const (id₌ (x ∘ r)))
          (const (project-pair₁ x y r)) (const (pair-β₁ (x ∘ r) (y ∘ r)))
    pair-pre-over₁  x y r =
      replace-edges₌ ((post-constant pr₁ (pair-pre x y r)) ⁻¹) (id₌ (const (id₌ (x ∘ r))))
        (constant-square₌ {X = A}
          ((comp₌-unitˡ-One (project-pair₁ x y r)) ⁻¹ ∙ pair-pre-triangle₁ x y r))

    pair-pre-over₂ : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      → SquareCell₌ (pr₂ ◁ const {P = A} (pair-pre x y r)) (const (id₌ (y ∘ r)))
          (const (project-pair₂ x y r)) (const (pair-β₂ (x ∘ r) (y ∘ r)))
    pair-pre-over₂  x y r =
      replace-edges₌ ((post-constant pr₂ (pair-pre x y r)) ⁻¹) (id₌ (const (id₌ (y ∘ r))))
        (constant-square₌ {X = A}
          ((comp₌-unitˡ-One (project-pair₂ x y r)) ⁻¹ ∙ pair-pre-triangle₂ x y r))

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-pre-over₁-One : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      → SquareCell₌ (pr₁ ◁ pair-pre x y r) (id₌ (x ∘ r))
          (project-pair₁ x y r) (pair-β₁ (x ∘ r) (y ∘ r))
    pair-pre-over₁-One x y r =
      (comp₌-unitˡ-One (project-pair₁ x y r)) ⁻¹ ∙ pair-pre-triangle₁ x y r

    pair-pre-over₂-One : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      → SquareCell₌ (pr₂ ◁ pair-pre x y r) (id₌ (y ∘ r))
          (project-pair₂ x y r) (pair-β₂ (x ∘ r) (y ∘ r))
    pair-pre-over₂-One x y r =
      (comp₌-unitˡ-One (project-pair₂ x y r)) ⁻¹ ∙ pair-pre-triangle₂ x y r
```

## Paired evaluation

For `α : f ∘ r = f′` and `β : g ∘ r = g′`, the composite
`pair⁼ α β ∙ pair-pre f g r : pair f g ∘ r = pair f′ g′`, the paired
evaluation, lies over `α` and `β`. For families its sides are the constant
families of the projection laws; the `-One` instances have the laws
themselves as sides and the restriction `pair-pre f g r` itself.

```agda
module _ {Γ : Context} where
  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair-evaluation-over₁ : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      {f′ : MAP R C} {g′ : MAP R D}
      (α : ((x ∘ r) ＝ f′)) (β : ((y ∘ r) ＝ g′))
      → SquareCell₌ (pr₁ ◁ (pair⁼ α β ∙ const (pair-pre x y r))) α
          (const (project-pair₁ x y r)) (const (pair-β₁ f′ g′))
    pair-evaluation-over₁ x y r α β = replace-edges₌ (id₌ _) (comp₌-unitʳ α)
      (lies-over-comp pr₁ (pair-pre-over₁ x y r) (pair⁼-triangle₁ α β))

    pair-evaluation-over₂ : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      {f′ : MAP R C} {g′ : MAP R D}
      (α : ((x ∘ r) ＝ f′)) (β : ((y ∘ r) ＝ g′))
      → SquareCell₌ (pr₂ ◁ (pair⁼ α β ∙ const (pair-pre x y r))) β
          (const (project-pair₂ x y r)) (const (pair-β₂ f′ g′))
    pair-evaluation-over₂ x y r α β = replace-edges₌ (id₌ _) (comp₌-unitʳ β)
      (lies-over-comp pr₂ (pair-pre-over₂ x y r) (pair⁼-triangle₂ α β))

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-evaluation-over₁-One : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      {f′ : MAP R C} {g′ : MAP R D} (α : (x ∘ r) =₁ f′) (β : (y ∘ r) =₁ g′)
      → SquareCell₌ (pr₁ ◁ (pair⁼ α β ∙ pair-pre x y r)) α
          (project-pair₁ x y r) (pair-β₁ f′ g′)
    pair-evaluation-over₁-One x y r α β =
      replace-edges₌ (id₌ _) (comp₌-unitʳ-One α)
        (lies-over-comp pr₁ (pair-pre-over₁-One x y r) (pair⁼-triangle₁-One α β))

    pair-evaluation-over₂-One : {C D : CAT Γ} (x : Term C) (y : Term D) (r : MAP R X)
      {f′ : MAP R C} {g′ : MAP R D} (α : (x ∘ r) =₁ f′) (β : (y ∘ r) =₁ g′)
      → SquareCell₌ (pr₂ ◁ (pair⁼ α β ∙ pair-pre x y r)) β
          (project-pair₂ x y r) (pair-β₂ f′ g′)
    pair-evaluation-over₂-One x y r α β =
      replace-edges₌ (id₌ _) (comp₌-unitʳ-One β)
        (lies-over-comp pr₂ (pair-pre-over₂-One x y r) (pair⁼-triangle₂-One α β))
```

A fixed paired evaluation, as a constant family, is the paired evaluation of
the constant families.

```agda
  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-evaluation-const : {C D : CAT Γ} {x : Term C} {y : Term D} (r : MAP R X)
      {x′ : MAP R C} {y′ : MAP R D} (α : (x ∘ r) =₁ x′) (β : (y ∘ r) =₁ y′)
      → (pair⁼ (const {P = A} α) (const β) ∙ const (pair-pre x y r)) =₁
          const (pair⁼ α β ∙ pair-pre x y r)
    pair-evaluation-const {x = x} {y} r α β = const-comp (pair⁼ α β) (pair-pre x y r) ∙
      comp₌-cong (pair⁼-constant α β) (id₌ (const (pair-pre x y r)))
```

## Naturality of restriction

A family `ε : pair f g ∘ r = pair f′ g′ ∘ s` lying over `α` and `β` along
the restricted projection laws forms a square with `pair⁼ α β` and the two
restrictions. Restricting a pairing, changing the restricting functor, and
both at once are instances.

```agda
module _ {Γ : Context} where
  private
    module _ {A R X : CAT Γ} where
      open Terms.InContext X using (Term)
      open Terms.Equalities A using (_＝_)

      evaluation-square : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
        {r s : MAP R X}
        (ε : ((pair x y ∘ r) ＝ (pair x′ y′ ∘ s)))
        (α : ((x ∘ r) ＝ (x′ ∘ s))) (β : ((y ∘ r) ＝ (y′ ∘ s)))
        → SquareCell₌ (pr₁ ◁ ε) α (const (project-pair₁ x y r)) (const (project-pair₁ x′ y′ s))
        → SquareCell₌ (pr₂ ◁ ε) β (const (project-pair₂ x y r)) (const (project-pair₂ x′ y′ s))
        → SquareCell₌ ε (pair⁼ α β) (const (pair-pre x y r)) (const (pair-pre x′ y′ s))
      evaluation-square {x = x} {x′} {y} {y′} {r} {s} ε α β first second = pair₌-unique
        (replace-edges₌ (id₌ _) (comp₌-unitˡ α)
          (lies-over-comp pr₁ first (pair-pre-over₁ x′ y′ s)))
        (replace-edges₌ (id₌ _) (comp₌-unitˡ β)
          (lies-over-comp pr₂ second (pair-pre-over₂ x′ y′ s)))
        (pair-evaluation-over₁ x y r α β)
        (pair-evaluation-over₂ x y r α β)

  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair-pre-natural-substitution : {C D : CAT Γ}
      (x : Term C) (y : Term D) {r s : MAP R X} (γ : r ＝ s)
      → SquareCell₌ (pair x y ◁ γ) (pair⁼ (x ◁ γ) (y ◁ γ))
          (const (pair-pre x y r)) (const (pair-pre x y s))
    pair-pre-natural-substitution x y γ =
      evaluation-square (pair x y ◁ γ) (x ◁ γ) (y ◁ γ)
        (restrict-change-square pr₁ (pair x y) x (pair-β₁ x y) γ)
        (restrict-change-square pr₂ (pair x y) y (pair-β₂ x y) γ)

    pair-pre-natural : {C D : CAT Γ}
      {x x′ : Term C} {y y′ : Term D} {r s : MAP R X}
      (α : x ＝ x′) (β : y ＝ y′) (γ : r ＝ s)
      → N.NaturalityAt (RestrictionBefore R X C D) (RestrictionAfter R X C D)
          (λ q → pair-pre (N.Inputs₃.first q) (N.Inputs₃.second q) (N.Inputs₃.third q))
          (N.inputs₃ α β γ)
    pair-pre-natural {x = x} {x′} {y} {y′} {r} {s} α β γ =
      evaluation-square (pair⁼ α β ⋆ γ) (α ⋆ γ) (β ⋆ γ)
        (lies-over-comp pr₁ (restrict-change-square pr₁ (pair x y) x (pair-β₁ x y) γ)
          (restrict-square pr₁ (pair⁼ α β) α (pair-β₁ x y) (pair-β₁ x′ y′) s
            (pair⁼-triangle₁ α β)))
        (lies-over-comp pr₂ (restrict-change-square pr₂ (pair x y) y (pair-β₂ x y) γ)
          (restrict-square pr₂ (pair⁼ α β) β (pair-β₂ x y) (pair-β₂ x′ y′) s
            (pair⁼-triangle₂ α β)))

  pair-pre-naturality : (R X C D : CAT Γ)
    → N.Naturality (RestrictionBefore R X C D) (RestrictionAfter R X C D)
        (λ q → pair-pre (N.Inputs₃.first q) (N.Inputs₃.second q) (N.Inputs₃.third q))
  pair-pre-naturality R X C D {X = P} {i} {j} (N.inputs₃ α β γ) =
    pair-pre-natural {A = P} {R = R} {X = X} {C = C} {D = D}
      {x = N.Inputs₃.first i} {x′ = N.Inputs₃.first j}
      {y = N.Inputs₃.second i} {y′ = N.Inputs₃.second j}
      {r = N.Inputs₃.third i} {s = N.Inputs₃.third j} α β γ

  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair-pre-natural-inputs : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x ＝ x′) (β : y ＝ y′) (r : MAP R X)
      → SquareCell₌ (pair⁼ α β ▷ r) (pair⁼ (α ▷ r) (β ▷ r))
          (const (pair-pre x y r)) (const (pair-pre x′ y′ r))
    pair-pre-natural-inputs {C = C} {D} {x} {x′} {y} {y′} α β r =
      let fix : N.Inputs₂ (MAP X C) (MAP X D) → RestrictionInputs R X C D
          fix q = N.inputs₃ (N.Inputs₂.first q) (N.Inputs₂.second q) r
          change : {P : CAT Γ} {i j : N.Inputs₂ (MAP X C) (MAP X D)}
            → N.PairChange (N.HomChange X C) (N.HomChange X D) P i j
            → RestrictionChange R X C D P (fix i) (fix j)
          change δ = N.inputs₃ (N.Inputs₂.first δ) (N.Inputs₂.second δ) (const (id₌ r))
          F : N.Operation (N.Inputs₂ (MAP X C) (MAP X D))
            (N.PairChange (N.HomChange X C) (N.HomChange X D)) R (C × D)
          F = N.Substitute (RestrictionBefore R X C D) fix change
          G : N.Operation (N.Inputs₂ (MAP X C) (MAP X D))
            (N.PairChange (N.HomChange X C) (N.HomChange X D)) R (C × D)
          G = N.Substitute (RestrictionAfter R X C D) fix change
          top : N.Action F
          top δ = pair⁼ (N.Inputs₂.first δ) (N.Inputs₂.second δ) ▷ r
          bottom : N.Action G
          bottom δ = pair⁼ (N.Inputs₂.first δ ▷ r) (N.Inputs₂.second δ ▷ r)
          top-law : {P : CAT Γ} {i j : N.Inputs₂ (MAP X C) (MAP X D)}
            (δ : N.PairChange (N.HomChange X C) (N.HomChange X D) P i j)
            → N.Operation.action F δ =₁ top δ
          top-law δ = hcomp-id-inner (pair⁼ (N.Inputs₂.first δ) (N.Inputs₂.second δ)) r
          bottom-law : {P : CAT Γ} {i j : N.Inputs₂ (MAP X C) (MAP X D)}
            (δ : N.PairChange (N.HomChange X C) (N.HomChange X D) P i j)
            → N.Operation.action G δ =₁ bottom δ
          bottom-law δ = pair⁼-cong (hcomp-id-inner (N.Inputs₂.first δ) r)
            (hcomp-id-inner (N.Inputs₂.second δ) r)
          joint : N.Naturality F G
            (λ q → pair-pre (N.Inputs₂.first q) (N.Inputs₂.second q) r)
          joint = N.naturality-substitute {F = RestrictionBefore R X C D} {G = RestrictionAfter R X C D}
            fix change (pair-pre-naturality R X C D)
      in N.naturality-transport {F = F} {G = G} top bottom top-law bottom-law joint
          {i = N.inputs₂ x y} {j = N.inputs₂ x′ y′} (N.inputs₂ α β)

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-pre-natural-inputs-One : {C D : CAT Γ} {x x′ : Term C} {y y′ : Term D}
      (α : x =₁ x′) (β : y =₁ y′) (r : MAP R X)
      → SquareCell₌ (pair⁼ α β ▷ r) (pair⁼ (α ▷ r) (β ▷ r))
          (pair-pre x y r) (pair-pre x′ y′ r)
    pair-pre-natural-inputs-One α β r = unconst-sides₌ (pair-pre-natural-inputs α β r)

    pair-pre-natural-substitution-One : {C D : CAT Γ}
      (x : Term C) (y : Term D) {r s : MAP R X} (γ : r =₁ s)
      → SquareCell₌ (pair x y ◁ γ) (pair⁼ (x ◁ γ) (y ◁ γ))
          (pair-pre x y r) (pair-pre x y s)
    pair-pre-natural-substitution-One x y γ =
      unconst-sides₌ (pair-pre-natural-substitution x y γ)

    pair-pre-natural-One : {C D : CAT Γ}
      {x x′ : Term C} {y y′ : Term D} {r s : MAP R X}
      (α : x =₁ x′) (β : y =₁ y′) (γ : r =₁ s)
      → SquareCell₌ (pair⁼ α β ⋆ γ) (pair⁼ (α ⋆ γ) (β ⋆ γ))
          (pair-pre x y r) (pair-pre x′ y′ s)
    pair-pre-natural-One α β γ = unconst-sides₌ (pair-pre-natural α β γ)
```

The three inputs can vary independently: the universal instance is
parameterized by the product of the three identification animae, with the
projections as families. It is a single family of squares, not a choice of
a square at each individual input.

```agda
  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    module ThreeInputs {C D : CAT Γ}
      (f f′ : Term C) (g g′ : Term D) (r s : MAP R X) where

      Parameter : CAT Γ
      Parameter = ((Equal f f′) × (Equal g g′)) × (Equal r s)

      open Terms.Equalities Parameter using (_＝_)

      α : f ＝ f′
      α = pr₁ ∘ pr₁

      β : g ＝ g′
      β = pr₂ ∘ pr₁

      γ : r ＝ s
      γ = pr₂

      naturality : SquareCell₌ (pair⁼ α β ⋆ γ) (pair⁼ (α ⋆ γ) (β ⋆ γ))
        (const (pair-pre f g r)) (const (pair-pre f′ g′ s))
      naturality = pair-pre-natural α β γ
```

## Units and iterated restriction

Restricting along an identity agrees with the right unitor. Restricting
along `σ ∘ τ` agrees with restricting along `σ` and then along `τ`. In both
cases the two sides lie over the same pair of identifications: the unitor
and associator of the coordinates.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-pre-id : {C D : CAT Γ} (x : Term C) (y : Term D)
      → (pair⁼ (comp-unitʳ x) (comp-unitʳ y) ∙ pair-pre x y (id X)) =₂
          comp-unitʳ (pair x y)
    pair-pre-id x y = pair₌-unique
      (pair-evaluation-over₁-One x y (id _) (comp-unitʳ x) (comp-unitʳ y))
      (pair-evaluation-over₂-One x y (id _) (comp-unitʳ x) (comp-unitʳ y))
      ((restrict-triangle-id pr₁ (pair x y) x (pair-β₁ x y)) ⁻¹)
      ((restrict-triangle-id pr₂ (pair x y) y (pair-β₂ x y)) ⁻¹)

  module IteratedRestriction {Q R X C D : CAT Γ}
    (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R) where

    source : MAP Q (C × D)
    source = (pair f g ∘ σ) ∘ τ

    target : MAP Q (C × D)
    target = pair (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ))

    together : source =₁ target
    together = pair-pre f g (σ ∘ τ) ∙ comp-assoc τ σ (pair f g)

    successively : source =₁ target
    successively = pair⁼ (comp-assoc τ σ f) (comp-assoc τ σ g) ∙
      (pair-pre (f ∘ σ) (g ∘ σ) τ ∙ (pair-pre f g σ ▷ τ))

    private
      reduce : {E : CAT Γ} {x : MAP X E} (a : ((x ∘ σ) ∘ τ) =₁ (x ∘ (σ ∘ τ)))
        → (a ∙ (id₌ _ ∙ id₌ _)) =₂ a
      reduce a = comp₌-unitʳ-One a ∙ comp₌-cong (id₌ a) (comp₌-unitˡ-One (id₌ _))

      together-over₁ = replace-edges₌ (id₌ _) (comp₌-unitˡ-One (comp-assoc τ σ f))
        (lies-over-comp pr₁
          (restrict-triangle-assoc pr₁ (pair f g) (pair-β₁ f g) σ τ)
          (pair-pre-over₁-One f g (σ ∘ τ)))
      together-over₂ = replace-edges₌ (id₌ _) (comp₌-unitˡ-One (comp-assoc τ σ g))
        (lies-over-comp pr₂
          (restrict-triangle-assoc pr₂ (pair f g) (pair-β₂ f g) σ τ)
          (pair-pre-over₂-One f g (σ ∘ τ)))

      restricted-over₁ = replace-edges₌ (id₌ _) (preWhisker-id₌ (f ∘ σ) τ)
          (restrict-square-One pr₁ (pair-pre f g σ) (id₌ (f ∘ σ))
            (project-pair₁ f g σ) (pair-β₁ (f ∘ σ) (g ∘ σ)) τ
            ((comp₌-unitˡ-One (project-pair₁ f g σ)) ⁻¹ ∙ pair-pre-triangle₁ f g σ))
      restricted-over₂ = replace-edges₌ (id₌ _) (preWhisker-id₌ (g ∘ σ) τ)
          (restrict-square-One pr₂ (pair-pre f g σ) (id₌ (g ∘ σ))
            (project-pair₂ f g σ) (pair-β₂ (f ∘ σ) (g ∘ σ)) τ
            ((comp₌-unitˡ-One (project-pair₂ f g σ)) ⁻¹ ∙ pair-pre-triangle₂ f g σ))

      successively-over₁ = replace-edges₌ (id₌ _) (reduce (comp-assoc τ σ f))
        (lies-over-comp pr₁
          (lies-over-comp pr₁ restricted-over₁ (pair-pre-over₁-One (f ∘ σ) (g ∘ σ) τ))
          (pair⁼-triangle₁-One (comp-assoc τ σ f) (comp-assoc τ σ g)))
      successively-over₂ = replace-edges₌ (id₌ _) (reduce (comp-assoc τ σ g))
        (lies-over-comp pr₂
          (lies-over-comp pr₂ restricted-over₂ (pair-pre-over₂-One (f ∘ σ) (g ∘ σ) τ))
          (pair⁼-triangle₂-One (comp-assoc τ σ f) (comp-assoc τ σ g)))

    compatibility : together =₂ successively
    compatibility = pair₌-unique together-over₁ together-over₂
      successively-over₁ successively-over₂

  module _ {Q R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-pre-iterated : {C D : CAT Γ}
      (x : Term C) (y : Term D) (σ : MAP R X) (τ : MAP Q R)
      → IteratedRestriction.together x y σ τ =₂ IteratedRestriction.successively x y σ τ
    pair-pre-iterated = IteratedRestriction.compatibility
```

## Naturality of evaluation

A family of functors `f`, `g` evaluated at `r` and normalized by `b`, `d`
is natural in `r`: an identification `δ : r = s` with squares relating the
normalizations gives a square of the paired evaluations. Composing with the
universal composition functor gives the naturality of `comp₌-evaluate-One`, and
the terminal case gives the naturality of `const-evaluate`.

```agda
module _ {Γ : Context} where
  private
    module _ {X : CAT Γ} where
      open Terms.InContext X using (Term)

      post-triangle-inner-One : {K C D : CAT Γ} (F : MAP C D) (π : MAP K C)
        {t t′ : Term K} {p p′ : Term C}
        (δ : t =₁ t′) (α : p =₁ p′) (b : (π ∘ t) =₁ p) (b′ : (π ∘ t′) =₁ p′)
        → SquareCell₌ (π ◁ δ) α b b′
        → SquareCell₌ ((F ∘ π) ◁ δ) (F ◁ α) (post-triangle F π t b) (post-triangle F π t′ b′)
      post-triangle-inner-One F π δ α b b′ square =
        unconst-sides₌ (post-triangle-inner F π δ α b b′ (const-sides₌ square))

    identity-square-One : {C D : CAT Γ} {f g : MAP C D} (α : f =₁ g)
      → SquareCell₌ α α (id₌ f) (id₌ g)
    identity-square-One α = unconst-sides₌ (identity-square₌ α)

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    module _ {A : CAT Γ} where
      open Terms.Equalities A using (_＝_)

      pair-evaluation-natural : {K C D : CAT Γ} (f : MAP K C) (g : MAP K D)
        {r s : Term K} (δ : r ＝ s)
        {x x′ : Term C} {y y′ : Term D}
        (b : (f ∘ r) ＝ x) (b′ : (f ∘ s) ＝ x′)
        (d : (g ∘ r) ＝ y) (d′ : (g ∘ s) ＝ y′)
        (α : x ＝ x′) (β : y ＝ y′)
        → SquareCell₌ (f ◁ δ) α b b′
        → SquareCell₌ (g ◁ δ) β d d′
        → SquareCell₌ (pair f g ◁ δ) (pair⁼ α β)
            (pair⁼ b d ∙ const (pair-pre f g r)) (pair⁼ b′ d′ ∙ const (pair-pre f g s))
      pair-evaluation-natural f g {r} {s} δ b b′ d d′ α β p q = pair₌-unique
        (replace-edges₌ (id₌ _) p
          (lies-over-comp pr₁
            (restrict-change-square pr₁ (pair f g) f (pair-β₁ f g) δ)
            (pair-evaluation-over₁ f g s b′ d′)))
        (replace-edges₌ (id₌ _) q
          (lies-over-comp pr₂
            (restrict-change-square pr₂ (pair f g) g (pair-β₂ f g) δ)
            (pair-evaluation-over₂ f g s b′ d′)))
        (lies-over-comp pr₁ (pair-evaluation-over₁ f g r b d)
          (pair⁼-triangle₁ α β))
        (lies-over-comp pr₂ (pair-evaluation-over₂ f g r b d)
          (pair⁼-triangle₂ α β))

    pair-evaluation-natural-One : {K C D : CAT Γ} (f : MAP K C) (g : MAP K D)
      {r s : Term K} (δ : r =₁ s)
      {x x′ : Term C} {y y′ : Term D}
      (b : (f ∘ r) =₁ x) (b′ : (f ∘ s) =₁ x′)
      (d : (g ∘ r) =₁ y) (d′ : (g ∘ s) =₁ y′)
      (α : x =₁ x′) (β : y =₁ y′)
      → SquareCell₌ (f ◁ δ) α b b′
      → SquareCell₌ (g ◁ δ) β d d′
      → SquareCell₌ (pair f g ◁ δ) (pair⁼ α β)
          (pair⁼ b d ∙ pair-pre f g r) (pair⁼ b′ d′ ∙ pair-pre f g s)
    pair-evaluation-natural-One f g {r} {s} δ b b′ d d′ α β p q =
      replace-sides₌
        (comp₌-cong (id₌ (pair⁼ b d)) (const-One (pair-pre f g r)))
        (comp₌-cong (id₌ (pair⁼ b′ d′)) (const-One (pair-pre f g s)))
        (pair-evaluation-natural f g δ b b′ d d′ α β p q)
```

A paired evaluation is also natural in the paired functors: identifications
`u : x = x′` and `v : y = y′`, with squares relating the restricted
identifications to `α` and `β` along the evaluations, give a square of the
paired evaluations. This is the naturality of `pair-pre` in its inputs,
pasted with the pairing of the two coordinate squares.

```agda
  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    pair-evaluation-natural-inputs : {C D : CAT Γ}
      {x x′ : Term C} {y y′ : Term D} (u : x ＝ x′) (v : y ＝ y′) (r : MAP R X)
      {x₁ x₁′ : MAP R C} {y₁ y₁′ : MAP R D}
      (e : (x ∘ r) ＝ x₁) (e′ : (x′ ∘ r) ＝ x₁′)
      (d : (y ∘ r) ＝ y₁) (d′ : (y′ ∘ r) ＝ y₁′)
      (α : x₁ ＝ x₁′) (β : y₁ ＝ y₁′)
      → SquareCell₌ (u ▷ r) α e e′
      → SquareCell₌ (v ▷ r) β d d′
      → SquareCell₌ (pair⁼ u v ▷ r) (pair⁼ α β)
          (pair⁼ e d ∙ const (pair-pre x y r)) (pair⁼ e′ d′ ∙ const (pair-pre x′ y′ r))
    pair-evaluation-natural-inputs u v r e e′ d d′ α β p q =
      paste-square₌ (pair-pre-natural-inputs u v r) (pair⁼-square p q)

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-evaluation-natural-inputs-One : {C D : CAT Γ}
      {x x′ : Term C} {y y′ : Term D} (u : x =₁ x′) (v : y =₁ y′) (r : MAP R X)
      {x₁ x₁′ : MAP R C} {y₁ y₁′ : MAP R D}
      (e : (x ∘ r) =₁ x₁) (e′ : (x′ ∘ r) =₁ x₁′)
      (d : (y ∘ r) =₁ y₁) (d′ : (y′ ∘ r) =₁ y₁′)
      (α : x₁ =₁ x₁′) (β : y₁ =₁ y₁′)
      → SquareCell₌ (u ▷ r) α e e′
      → SquareCell₌ (v ▷ r) β d d′
      → SquareCell₌ (pair⁼ u v ▷ r) (pair⁼ α β)
          (pair⁼ e d ∙ pair-pre x y r) (pair⁼ e′ d′ ∙ pair-pre x′ y′ r)
    pair-evaluation-natural-inputs-One {x = x} {x′} {y} {y′} u v r e e′ d d′ α β p q =
      replace-sides₌
        (comp₌-cong (id₌ (pair⁼ e d)) (const-One (pair-pre x y r)))
        (comp₌-cong (id₌ (pair⁼ e′ d′)) (const-One (pair-pre x′ y′ r)))
        (pair-evaluation-natural-inputs u v r e e′ d d′ α β p q)

  const-evaluate-natural : {X C : CAT Γ} (x : Obj-abs C)
    {r s : Obj-abs X} (δ : r =₁ s)
    → SquareCell₌ (const x ◁ δ) (id₌ x) (const-evaluate x r) (const-evaluate x s)
  const-evaluate-natural {X} x {r} {s} δ =
    let b = terminal-identification (terminate X ∘ r) (terminate One)
        b′ = terminal-identification (terminate X ∘ s) (terminate One)
        unit = replace-edges₌ ((postWhisker-id₌ x (terminate One)) ⁻¹) (id₌ (id₌ x))
          (transpose-square₌ (identity-square-One (const-One x)))
    in paste-square₌
      (post-triangle-inner-One x (terminate X) δ (id₌ (terminate One)) b b′
        (terminal-unique₂ _ _))
      unit

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    module _ {A : CAT Γ} where
      open Terms.Equalities A using (_＝_)

      comp₌-evaluate-natural : {K C D : CAT Γ} {f g h : MAP C D}
        (β : MAP K (Equal g h)) (α : MAP K (Equal f g))
        {r s : Term K} (δ : r ＝ s)
        {x x′ : Term (Equal g h)} {y y′ : Term (Equal f g)}
        (b : (β ∘ r) ＝ x) (b′ : (β ∘ s) ＝ x′)
        (d : (α ∘ r) ＝ y) (d′ : (α ∘ s) ＝ y′)
        (ξ : x ＝ x′) (η : y ＝ y′)
        → SquareCell₌ (β ◁ δ) ξ b b′
        → SquareCell₌ (α ◁ δ) η d d′
        → SquareCell₌ ((β ∙ α) ◁ δ) (comp₌ ◁ pair⁼ ξ η)
            (comp₌-evaluate β α r b d) (comp₌-evaluate β α s b′ d′)
      comp₌-evaluate-natural {K} {f = f} {g} {h} β α {r} {s} δ b b′ d d′ ξ η p q =
        let normalize : (t : Term K) {u : Term (Equal g h)} {v : Term (Equal f g)}
              (e : (β ∘ t) ＝ u) (k : (α ∘ t) ＝ v)
              → ((comp₌ ◁ (pair⁼ e k ∙ const (pair-pre β α t))) ∙
                  const (comp-assoc t (pair β α) comp₌)) =₁ comp₌-evaluate β α t e k
            normalize t e k =
              comp₌-cong (id₌ (comp₌ ◁ pair⁼ e k))
                (const-comp (comp₌ ◁ pair-pre β α t) (comp-assoc t (pair β α) comp₌) ∙
                  comp₌-cong (post-constant comp₌ (pair-pre β α t))
                    (id₌ (const (comp-assoc t (pair β α) comp₌)))) ∙
              (comp₌-assoc (comp₌ ◁ pair⁼ e k) (comp₌ ◁ const (pair-pre β α t))
                  (const (comp-assoc t (pair β α) comp₌)) ∙
                comp₌-cong (postWhisker-comp₌ comp₌ (pair⁼ e k) (const (pair-pre β α t)))
                  (id₌ (const (comp-assoc t (pair β α) comp₌))))
        in replace-sides₌ (normalize r b d) (normalize s b′ d′)
          (paste-square₌ (Whiskering.postWhisker-comp δ (pair β α) comp₌)
            (post-square₌ comp₌ (pair-evaluation-natural β α δ b b′ d d′ ξ η p q)))

    comp₌-evaluate-natural-One : {K C D : CAT Γ} {f g h : MAP C D}
      (β : MAP K (Equal g h)) (α : MAP K (Equal f g))
      {r s : Term K} (δ : r =₁ s)
      {x x′ : Term (Equal g h)} {y y′ : Term (Equal f g)}
      (b : (β ∘ r) =₁ x) (b′ : (β ∘ s) =₁ x′)
      (d : (α ∘ r) =₁ y) (d′ : (α ∘ s) =₁ y′)
      (ξ : x =₁ x′) (η : y =₁ y′)
      → SquareCell₌ (β ◁ δ) ξ b b′
      → SquareCell₌ (α ◁ δ) η d d′
      → SquareCell₌ ((β ∙ α) ◁ δ) (comp₌-cong ξ η)
          (comp₌-evaluate-One β α r b d) (comp₌-evaluate-One β α s b′ d′)
    comp₌-evaluate-natural-One β α {r} {s} δ b b′ d d′ ξ η p q =
      replace-sides₌
        (comp₌-cong (id₌ (comp₌-cong b d)) (const-One (comp₌-pre β α r)))
        (comp₌-cong (id₌ (comp₌-cong b′ d′)) (const-One (comp₌-pre β α s)))
        (comp₌-evaluate-natural β α δ b b′ d d′ ξ η p q)

  module _ {K : CAT Γ} where
    open Terms.Equalities K using (_＝_)

    const-comp-evaluate : {C D : CAT Γ} {f g h : MAP C D}
      (τ : g =₁ h) (F : f ＝ g) (r : Obj-abs K)
      → ((const τ ∙ F) ∘ r) =₁ (τ ∙ (F ∘ r))
    const-comp-evaluate τ F r =
      comp₌-evaluate-One (const τ) F r (const-evaluate τ r) (id₌ (F ∘ r))

    const-comp-evaluate-natural : {C D : CAT Γ} {f g h : MAP C D}
      (τ : g =₁ h) (F : f ＝ g) {r s : Obj-abs K} (δ : r =₁ s)
      → SquareCell₌ ((const τ ∙ F) ◁ δ) (comp₌-cong (id₌ τ) (F ◁ δ))
          (const-comp-evaluate τ F r) (const-comp-evaluate τ F s)
    const-comp-evaluate-natural τ F {r} {s} δ = comp₌-evaluate-natural-One (const τ) F δ
      (const-evaluate τ r) (const-evaluate τ s) (id₌ (F ∘ r)) (id₌ (F ∘ s))
      (id₌ τ) (F ◁ δ) (const-evaluate-natural τ δ) (identity-square-One (F ◁ δ))

    comp-const-evaluate : {C D : CAT Γ} {f g h : MAP C D}
      (F : g ＝ h) (τ : f =₁ g) (r : Obj-abs K)
      → ((F ∙ const τ) ∘ r) =₁ ((F ∘ r) ∙ τ)
    comp-const-evaluate F τ r =
      comp₌-evaluate-One F (const τ) r (id₌ (F ∘ r)) (const-evaluate τ r)

    comp-const-evaluate-natural : {C D : CAT Γ} {f g h : MAP C D}
      (F : g ＝ h) (τ : f =₁ g) {r s : Obj-abs K} (δ : r =₁ s)
      → SquareCell₌ ((F ∙ const τ) ◁ δ) (comp₌-cong (F ◁ δ) (id₌ τ))
          (comp-const-evaluate F τ r) (comp-const-evaluate F τ s)
    comp-const-evaluate-natural F τ {r} {s} δ = comp₌-evaluate-natural-One F (const τ) δ
      (id₌ (F ∘ r)) (id₌ (F ∘ s)) (const-evaluate τ r) (const-evaluate τ s)
      (F ◁ δ) (id₌ τ) (identity-square-One (F ◁ δ)) (const-evaluate-natural τ δ)
```

## The projection pairing

`pair-projections : pair pr₁ pr₂ = id` has the expected projection triangles,
and restricting it along a pairing `pair f g` agrees with the paired
evaluation of the projection laws of `f` and `g`.

```agda
module _ {Γ : Context} where
  pair-projections-triangle₁ : {C D : CAT Γ}
    → (comp-unitʳ pr₁ ∙ (pr₁ ◁ pair-projections {C = C} {D = D})) =₂ pair-β₁ pr₁ pr₂
  pair-projections-triangle₁ =
    comp-inv-left (comp-unitʳ pr₁) (pair-β₁ pr₁ pr₂) ∙
      comp₌-cong (id₌ (comp-unitʳ pr₁))
        (pair₌-β₁ ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
          ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂))

  pair-projections-triangle₂ : {C D : CAT Γ}
    → (comp-unitʳ pr₂ ∙ (pr₂ ◁ pair-projections {C = C} {D = D})) =₂ pair-β₂ pr₁ pr₂
  pair-projections-triangle₂ =
    comp-inv-left (comp-unitʳ pr₂) (pair-β₂ pr₁ pr₂) ∙
      comp₌-cong (id₌ (comp-unitʳ pr₂))
        (pair₌-β₂ ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
          ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    pair-projections-pre : {A B : CAT Γ} (x : Term A) (y : Term B)
      → (comp-unitˡ (pair x y) ∙ (pair-projections ▷ pair x y)) =₂
          (pair⁼ (pair-β₁ x y) (pair-β₂ x y) ∙ pair-pre pr₁ pr₂ (pair x y))
    pair-projections-pre x y =
      let s = pair x y
      in pair₌-unique
        (comp₌-cong (id₌ (pair-β₁ x y))
          (identity-pre-coordinate pr₁ s (pair pr₁ pr₂) pair-projections
            (pair-β₁ pr₁ pr₂) pair-projections-triangle₁))
        (comp₌-cong (id₌ (pair-β₂ x y))
          (identity-pre-coordinate pr₂ s (pair pr₁ pr₂) pair-projections
            (pair-β₂ pr₁ pr₂) pair-projections-triangle₂))
        (pair-evaluation-over₁-One pr₁ pr₂ s (pair-β₁ x y) (pair-β₂ x y))
        (pair-evaluation-over₂-One pr₁ pr₂ s (pair-β₁ x y) (pair-β₂ x y))
```

## Restricting a triple

The left-nested triple `pair (pair g f) x` is restricted along `r` by
restricting the inner pair and then the outer pair. The three projection
laws of the restricted triple are compatible with the restriction.

```agda
module _ {Γ : Context} where
  module _ {R T : CAT Γ} where
    open Terms.InContext T using (Term)

    module TripleRestriction {A B C : CAT Γ}
      (g : Term A) (f : Term B) (x : Term C) (r : MAP R T) where

      open Triple g f x public using (triple; first; second; third)
      private
        module Restricted = Triple (g ∘ r) (f ∘ r) (x ∘ r)

      triple′ : MAP R ((A × B) × C)
      triple′ = Restricted.triple

      first′ : ((pr₁ ∘ pr₁) ∘ triple′) =₁ (g ∘ r)
      first′ = Restricted.first

      second′ : ((pr₂ ∘ pr₁) ∘ triple′) =₁ (f ∘ r)
      second′ = Restricted.second

      third′ : (pr₂ ∘ triple′) =₁ (x ∘ r)
      third′ = Restricted.third

      pair-change : (pair g f ∘ r) =₁ pair (g ∘ r) (f ∘ r)
      pair-change = pair-pre g f r

      triple-change : (triple ∘ r) =₁ triple′
      triple-change = pair⁼ pair-change (id₌ (x ∘ r)) ∙ pair-pre (pair g f) x r

      abstract
        first-projection : SquareCell₌ (pr₁ ◁ triple-change) pair-change
          (project-pair₁ (pair g f) x r) (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))
        first-projection =
          pair-evaluation-over₁-One (pair g f) x r pair-change (id₌ (x ∘ r))

        second-projection : SquareCell₌ (pr₂ ◁ triple-change) (id₌ (x ∘ r))
          (project-pair₂ (pair g f) x r) third′
        second-projection =
          pair-evaluation-over₂-One (pair g f) x r pair-change (id₌ (x ∘ r))

      abstract
        third-restriction :
          (third′ ∙ ((pr₂ ◁ triple-change) ∙ comp-assoc r triple pr₂)) =₂ (third ▷ r)
        third-restriction = comp₌-unitˡ-One (third ▷ r) ∙
          unrestrict-square pr₂ triple r triple′ triple-change third third′ (id₌ (x ∘ r))
            second-projection

      abstract
        nested-projection : {K : CAT Γ} (π : MAP (A × B) K)
          {v : Term K} (b : (π ∘ pair g f) =₁ v)
          (b′ : (π ∘ pair (g ∘ r) (f ∘ r)) =₁ (v ∘ r))
          → (b′ ∙ (π ◁ pair-change)) =₂ restrict-triangle π (pair g f) b r
          → ((b′ ∙ post-triangle π pr₁ triple′ (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))) ∙
              (((π ∘ pr₁) ◁ triple-change) ∙ comp-assoc r triple (π ∘ pr₁))) =₂
            ((b ∙ post-triangle π pr₁ triple (pair-β₁ (pair g f) x)) ▷ r)
        nested-projection π {v} b b′ triangle =
          let old = post-triangle π pr₁ triple (pair-β₁ (pair g f) x)
              new = post-triangle π pr₁ triple′ (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))
              tail = ((π ∘ pr₁) ◁ triple-change) ∙ comp-assoc r triple (π ∘ pr₁)
              A′ = comp-assoc r (pair g f) π
              coordinate = post-triangle-change π pr₁ triple r triple′ triple-change
                (pair-β₁ (pair g f) x) (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))
                pair-change first-projection
              projection = comp₌-unitˡ-One (b ▷ r) ∙
                unrestrict-square π (pair g f) r (pair (g ∘ r) (f ∘ r)) pair-change b b′
                  (id₌ (v ∘ r)) ((comp₌-unitˡ-One _) ⁻¹ ∙ triangle)
              rearrange = (comp₌-assoc b′ ((π ◁ pair-change) ∙ A′) (old ▷ r)) ⁻¹ ∙
                comp₌-cong (id₌ b′) ((comp₌-assoc (π ◁ pair-change) A′ (old ▷ r)) ⁻¹)
          in (preWhisker-comp₌ b old r) ⁻¹ ∙
            (comp₌-cong projection (id₌ (old ▷ r)) ∙
              (rearrange ∙ (comp₌-cong (id₌ b′) coordinate ∙ comp₌-assoc b′ new tail)))

      abstract
        first-restriction :
          (first′ ∙ (((pr₁ ∘ pr₁) ◁ triple-change) ∙ comp-assoc r triple (pr₁ ∘ pr₁))) =₂
          (first ▷ r)
        first-restriction = nested-projection pr₁ (pair-β₁ g f) (pair-β₁ (g ∘ r) (f ∘ r))
          (pair-pre-triangle₁ g f r)

        second-restriction :
          (second′ ∙ (((pr₂ ∘ pr₁) ◁ triple-change) ∙ comp-assoc r triple (pr₂ ∘ pr₁))) =₂
          (second ▷ r)
        second-restriction = nested-projection pr₂ (pair-β₂ g f) (pair-β₂ (g ∘ r) (f ∘ r))
          (pair-pre-triangle₂ g f r)
```
