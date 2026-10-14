# Specializing parameterized laws

The coherence axioms are laws between particular universal families of
identifications. This module restricts those laws along functors and
identifies the resulting boundaries with the expressions needed in
applications. It has four parts:

1. Restriction and evaluation: the general specialization rule, the
   behaviour of the operations under change of parameter, and constants.
2. The vertical calculus: units, inverses, associativity and their
   consequences for families with an arbitrary common parameter.
3. Naturality of unitors and associators, with the normalization of
   horizontal composites with identity identifications.
4. Whiskering of vertical composites and interchange.

Every law here is stated for identification families with an arbitrary
common parameter category `X` in the ambient context. Individual
identifications are the case `X = One`; constants over `One` are related
to their values by `const-One`, an identification rather than a definitional
equality. The family statements carry the main names. Where such a name is
also the name of the universal axiom, the axiom is referred to with the
qualification `Coherence`. No additional axiom is introduced here, and each
proof uses only the axioms it names.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section02.Specialization where


open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
open Coherence using (id₌; inv₌; comp₌; comp-unitˡ; comp-unitʳ; comp-assoc;
  postWhisker-id₌; preWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus

```

## Part 1: restriction and evaluation

### Restricting a law and identifying its boundaries

Given a law `κ : f =₁ g` and a functor `r : MAP R X`, precomposition gives
`κ ▷ r : (f ∘ r) =₁ (g ∘ r)`. To obtain a law between chosen expressions
`f′` and `g′`, supply identifications `left : (f ∘ r) =₁ f′` and
`right : (g ∘ r) =₁ g′`. Specialization is restriction followed by this
change of endpoints. The endpoint change uses the common bracketing
`right ∙ (κ ▷ r ∙ left ⁻¹)`: first precompose with the inverse of the new
source identification, then postcompose with the new target identification.

```agda
module _ {Γ : Context} where
  specialize : {R X Y : CAT Γ} {f g : MAP X Y} {f′ g′ : MAP R Y}
    → f =₁ g → (r : MAP R X)
    → (f ∘ r) =₁ f′ → (g ∘ r) =₁ g′ → f′ =₁ g′
  specialize κ r left right = right ∙ ((κ ▷ r) ∙ left ⁻¹)

```

For example, the universal left unit law `Coherence.comp₌-unitˡ f g` concerns
the identity family `id (f ＝ g)`. Restricted along a family
`α : MAP X (f ＝ g)`, its source becomes `(const (id₌ g) ∙ id (f ＝ g)) ∘ α`
and its target becomes `id (f ＝ g) ∘ α`. Identifying these with
`const (id₌ g) ∙ α` and `α` gives the family unit law `comp₌-unitˡ α`
below. The following lemmas construct such boundary identifications.

### Operations under change of parameter

Three interfaces recur. The `-cong` lemmas replace identified inputs.
The `-pre` lemmas identify an operation restricted along `r` with the same
operation applied to the restricted inputs. The `-evaluate` lemmas combine
the two: they restrict, then identify the restricted inputs with given
families. For vertical composition the first two follow from `pair⁼` and
`pair-pre`; whiskering and inversion commute with restriction by the
functor associator.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    comp₌-cong : {C D : CAT Γ} {f g h : MAP C D}
      {β β′ : g ＝ h} {α α′ : f ＝ g}
      → β =₁ β′ → α =₁ α′ → (β ∙ α) =₁ (β′ ∙ α′)
    comp₌-cong b a = comp₌ ◁ pair⁼ b a

  module _ {R X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    comp₌-pre : {C D : CAT Γ} {f g h : MAP C D}
      (β : g ＝ h) (α : f ＝ g) (r : MAP R X)
      → ((β ∙ α) ∘ r) =₁ ((β ∘ r) ∙ (α ∘ r))
    comp₌-pre β α r = (comp₌ ◁ pair-pre β α r) ∙ comp-assoc r (pair β α) comp₌

    postWhisker-pre : {C D E : CAT Γ} {f g : MAP C D}
      (u : MAP D E) (α : f ＝ g) (r : MAP R X)
      → ((u ◁ α) ∘ r) =₁ (u ◁ (α ∘ r))
    postWhisker-pre u α r = comp-assoc r α (postWhisker u)

    preWhisker-pre : {B C D : CAT Γ} {f g : MAP C D}
      (α : f ＝ g) (k : MAP B C) (r : MAP R X)
      → ((α ▷ k) ∘ r) =₁ ((α ∘ r) ▷ k)
    preWhisker-pre α k r = comp-assoc r α (preWhisker k)

    ⁻¹-pre : {C D : CAT Γ} {f g : MAP C D}
      (α : f ＝ g) (r : MAP R X)
      → (α ⁻¹ ∘ r) =₁ ((α ∘ r) ⁻¹)
    ⁻¹-pre α r = comp-assoc r α inv₌

```

Horizontal composition is defined using whiskering and vertical composition,
so their compatibility lemmas give its precomposition and congruence laws.
`hcomp-apply` evaluates the universal horizontal composite `hcomp` on a pair
of families.

```agda
  module _ {R X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    hcomp-pre : {C D E : CAT Γ} {f f′ : MAP C D} {g g′ : MAP D E}
      (β : g ＝ g′) (α : f ＝ f′) (r : MAP R X)
      → ((β ⋆ α) ∘ r) =₁ ((β ∘ r) ⋆ (α ∘ r))
    hcomp-pre {f′ = f′} {g = g} β α r =
      comp₌-cong (preWhisker-pre β f′ r) (postWhisker-pre g α r)
      ∙ comp₌-pre (β ▷ f′) (g ◁ α) r

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    hcomp-cong : {C D E : CAT Γ} {f f′ : MAP C D} {g g′ : MAP D E}
      {β β′ : g ＝ g′} {α α′ : f ＝ f′}
      → β =₁ β′ → α =₁ α′ → (β ⋆ α) =₁ (β′ ⋆ α′)
    hcomp-cong {f′ = f′} {g = g} b a =
      comp₌-cong (preWhisker f′ ◁ b) (postWhisker g ◁ a)

    hcomp-apply : {C D E : CAT Γ} {f f′ : MAP C D} {g g′ : MAP D E}
      (β : g ＝ g′) (α : f ＝ f′)
      → (hcomp ∘ pair β α) =₁ (β ⋆ α)
    hcomp-apply β α = hcomp-cong (pair-β₁ β α) (pair-β₂ β α)
                     ∙ hcomp-pre pr₁ pr₂ (pair β α)

  module _ {A R X : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    comp₌-evaluate : {C D : CAT Γ} {f g h : MAP C D}
      (β : MAP X (Equal g h)) (α : MAP X (Equal f g)) (r : MAP R X)
      {β′ : MAP R (Equal g h)} {α′ : MAP R (Equal f g)}
      → (β ∘ r) ＝ β′ → (α ∘ r) ＝ α′ → ((β ∙ α) ∘ r) ＝ (β′ ∙ α′)
    comp₌-evaluate β α r b a = (comp₌ ◁ pair⁼ b a) ∙ const (comp₌-pre β α r)

    postWhisker-evaluate : {C D E : CAT Γ} {f g : MAP C D}
      (u : MAP D E) (α : MAP X (Equal f g)) (r : MAP R X)
      {α′ : MAP R (Equal f g)} → (α ∘ r) ＝ α′
      → ((u ◁ α) ∘ r) ＝ (u ◁ α′)
    postWhisker-evaluate u α r a =
      (postWhisker u ◁ a) ∙ const (postWhisker-pre u α r)

    preWhisker-evaluate : {B C D : CAT Γ} {f g : MAP C D}
      (α : MAP X (Equal f g)) (k : MAP B C) (r : MAP R X)
      {α′ : MAP R (Equal f g)} → (α ∘ r) ＝ α′
      → ((α ▷ k) ∘ r) ＝ (α′ ▷ k)
    preWhisker-evaluate α k r a =
      (preWhisker k ◁ a) ∙ const (preWhisker-pre α k r)

    hcomp-evaluate : {C D E : CAT Γ} {f f′ : MAP C D} {g g′ : MAP D E}
      (β : MAP X (Equal g g′)) (α : MAP X (Equal f f′)) (r : MAP R X)
      {β′ : MAP R (Equal g g′)} {α′ : MAP R (Equal f f′)}
      → (β ∘ r) ＝ β′ → (α ∘ r) ＝ α′
      → ((β ⋆ α) ∘ r) ＝ (β′ ⋆ α′)
    hcomp-evaluate {f′ = f′} {g = g} β α r b a =
      (comp₌ ◁ pair⁼ (preWhisker f′ ◁ b) (postWhisker g ◁ a))
      ∙ const (hcomp-pre β α r)

  comp₌-evaluate-One : {R X C D : CAT Γ} {f g h : MAP C D}
    (β : MAP X (Equal g h)) (α : MAP X (Equal f g)) (r : MAP R X)
    {β′ : MAP R (Equal g h)} {α′ : MAP R (Equal f g)}
    → (β ∘ r) =₁ β′ → (α ∘ r) =₁ α′
    → ((β ∙ α) ∘ r) =₁ (β′ ∙ α′)
  comp₌-evaluate-One β α r b a = comp₌-cong b a ∙ comp₌-pre β α r

  postWhisker-evaluate-One : {R X C D E : CAT Γ} {f g : MAP C D}
    (u : MAP D E) (α : MAP X (Equal f g)) (r : MAP R X)
    {α′ : MAP R (Equal f g)} → (α ∘ r) =₁ α′
    → ((u ◁ α) ∘ r) =₁ (u ◁ α′)
  postWhisker-evaluate-One u α r a = (postWhisker u ◁ a) ∙ postWhisker-pre u α r

  preWhisker-evaluate-One : {R X B C D : CAT Γ} {f g : MAP C D}
    (α : MAP X (Equal f g)) (k : MAP B C) (r : MAP R X)
    {α′ : MAP R (Equal f g)} → (α ∘ r) =₁ α′
    → ((α ▷ k) ∘ r) =₁ (α′ ▷ k)
  preWhisker-evaluate-One α k r a = (preWhisker k ◁ a) ∙ preWhisker-pre α k r

  hcomp-evaluate-One : {R X C D E : CAT Γ} {f f′ : MAP C D} {g g′ : MAP D E}
    (β : MAP X (Equal g g′)) (α : MAP X (Equal f f′)) (r : MAP R X)
    {β′ : MAP R (Equal g g′)} {α′ : MAP R (Equal f f′)}
    → (β ∘ r) =₁ β′ → (α ∘ r) =₁ α′
    → ((β ⋆ α) ∘ r) =₁ (β′ ⋆ α′)
  hcomp-evaluate-One β α r b a = hcomp-cong b a ∙ hcomp-pre β α r

```

### Constant families

A constant family `const x = x ∘ terminate P` is restricted to a constant
family by uniqueness of functors to `One`. `const-One` identifies a constant
family over `One` with its value, and `const-evaluate` evaluates a constant
family at an absolute object. Composition, inversion, congruence and
whiskering of constants are computed by restricting the corresponding
operation along `terminate P`; the whiskering cases are functor associators.

```agda
module _ {Γ : Context} where
  const-pre : {R X C : CAT Γ} (x : Obj-abs C) (r : MAP R X)
    → (const x ∘ r) =₁ (const x)
  const-pre {R} {X} x r =
    (x ◁ terminal-identification (terminate X ∘ r) (terminate R)) ∙ comp-assoc r (terminate X) x

  const-One : {C : CAT Γ} (x : Obj-abs C) → (const {P = One} x) =₁ x
  const-One x = comp-unitʳ x ∙ (x ◁ terminal-identification (terminate One) (id One))

  const-evaluate : {X C : CAT Γ} (x : Obj-abs C) (r : Obj-abs X)
    → (const x ∘ r) =₁ x
  const-evaluate x r = const-One x ∙ const-pre x r

  const-comp : {X C D : CAT Γ} {f g h : MAP C D}
    (β : g =₁ h) (α : f =₁ g)
    → (const {P = X} β ∙ const α) =₁ (const (β ∙ α))
  const-comp {X} β α = (comp₌-pre β α (terminate X)) ⁻¹

  const-inv : {X C D : CAT Γ} {f g : MAP C D} (α : f =₁ g)
    → (const {P = X} (α ⁻¹)) =₁ ((const α) ⁻¹)
  const-inv {X} α = ⁻¹-pre α (terminate X)

  const-cong : {X C : CAT Γ} {x y : Obj-abs C}
    → x =₁ y → (const {P = X} x) =₁ (const y)
  const-cong {X} p = p ▷ terminate X

  post-constant : {A X C D : CAT Γ} {f g : MAP X C} (u : MAP C D) (α : f =₁ g)
    → (u ◁ const {P = A} α) =₁ (const (u ◁ α))
  post-constant {A} u α = (comp-assoc (terminate A) α (postWhisker u)) ⁻¹

  pre-constant : {A R X C : CAT Γ} {f g : MAP X C} (α : f =₁ g) (r : MAP R X)
    → (const {P = A} α ▷ r) =₁ (const (α ▷ r))
  pre-constant {A} α r = (comp-assoc (terminate A) α (preWhisker r)) ⁻¹

```

## Part 2: the vertical calculus

The vertical coherence axioms concern the universal families on
`f ＝ g` and on the right-nested product
`(h ＝ k) × ((g ＝ h) × (f ＝ g))`. Restricting them along an arbitrary
family, respectively along `pair γ (pair β α)`, gives the family laws.
The unit and inverse laws have constant identity families as boundaries.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    comp₌-unitˡ : {C D : CAT Γ} {f g : MAP C D} (α : f ＝ g)
      → (const (id₌ g) ∙ α) =₁ α
    comp₌-unitˡ {f = f} {g} α = specialize (Coherence.comp₌-unitˡ f g) α
      (comp₌-evaluate-One (const (id₌ g)) (id (Equal f g)) α
        (const-pre (id₌ g) α) (comp-unitˡ α))
      (comp-unitˡ α)

    comp₌-unitʳ : {C D : CAT Γ} {f g : MAP C D} (α : f ＝ g)
      → (α ∙ const (id₌ f)) =₁ α
    comp₌-unitʳ {f = f} {g} α = specialize (Coherence.comp₌-unitʳ f g) α
      (comp₌-evaluate-One (id (Equal f g)) (const (id₌ f)) α
        (comp-unitˡ α) (const-pre (id₌ f) α))
      (comp-unitˡ α)

    comp₌-inverseˡ : {C D : CAT Γ} {f g : MAP C D} (α : f ＝ g)
      → (α ⁻¹ ∙ α) =₁ (const (id₌ f))
    comp₌-inverseˡ {f = f} {g} α = specialize (Coherence.comp₌-inverseˡ f g) α
      (comp₌-evaluate-One ((id (Equal f g)) ⁻¹) (id (Equal f g)) α
        ((inv₌ ◁ comp-unitˡ α) ∙ ⁻¹-pre (id (Equal f g)) α) (comp-unitˡ α))
      (const-pre (id₌ f) α)

    comp₌-inverseʳ : {C D : CAT Γ} {f g : MAP C D} (α : f ＝ g)
      → (α ∙ α ⁻¹) =₁ (const (id₌ g))
    comp₌-inverseʳ {f = f} {g} α = specialize (Coherence.comp₌-inverseʳ f g) α
      (comp₌-evaluate-One (id (Equal f g)) ((id (Equal f g)) ⁻¹) α
        (comp-unitˡ α) ((inv₌ ◁ comp-unitˡ α) ∙ ⁻¹-pre (id (Equal f g)) α))
      (const-pre (id₌ g) α)

```

Associativity restricts the primitive law directly along the right-nested
pair of its three inputs, matching the bracketing of its parameter category.
The three projection computations are displayed.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    comp₌-assoc : {C D : CAT Γ} {f g h k : MAP C D}
      (γ : h ＝ k) (β : g ＝ h) (α : f ＝ g)
      → ((γ ∙ β) ∙ α) =₁ (γ ∙ (β ∙ α))
    comp₌-assoc {f = f} {g} {h} {k} γ β α =
      let parameters = pair γ (pair β α)
          first : (pr₁ ∘ parameters) =₁ γ
          first = pair-β₁ γ (pair β α)
          second : ((pr₁ ∘ pr₂) ∘ parameters) =₁ β
          second = pair-β₁ β α ∙
            ((pr₁ ◁ pair-β₂ γ (pair β α)) ∙ comp-assoc parameters pr₂ pr₁)
          third : ((pr₂ ∘ pr₂) ∘ parameters) =₁ α
          third = pair-β₂ β α ∙
            ((pr₂ ◁ pair-β₂ γ (pair β α)) ∙ comp-assoc parameters pr₂ pr₂)
      in specialize (Coherence.comp₌-assoc f g h k) parameters
        (comp₌-evaluate-One (pr₁ ∙ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) parameters
          (comp₌-evaluate-One pr₁ (pr₁ ∘ pr₂) parameters first second) third)
        (comp₌-evaluate-One pr₁ ((pr₁ ∘ pr₂) ∙ (pr₂ ∘ pr₂)) parameters first
          (comp₌-evaluate-One (pr₁ ∘ pr₂) (pr₂ ∘ pr₂) parameters second third))

```

### Inverse reductions and reassociation

An inverse pair adjacent to a family cancels. In each name, `left` or `right`
indicates the side of the remaining family on which the pair occurs, and
`inv-comp` or `comp-inv` the order of the pair. The cancelled factor is
itself a family; for a fixed identification, use its constant family. Each
reduction reassociates, applies an inverse law and removes the unit. The
names `cancel-left` and `cancel-right` are reserved for cancelling a common
factor from an equation.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    inv-comp-left : {C D : CAT Γ} {f g h : MAP C D}
      (β : g ＝ h) (α : f ＝ g)
      → (β ⁻¹ ∙ (β ∙ α)) =₁ α
    inv-comp-left β α = comp₌-unitˡ α ∙
      (comp₌-cong (comp₌-inverseˡ β) (id₌ α) ∙ (comp₌-assoc (β ⁻¹) β α) ⁻¹)

    comp-inv-left : {C D : CAT Γ} {f g h : MAP C D}
      (β : g ＝ h) (α : f ＝ h)
      → (β ∙ (β ⁻¹ ∙ α)) =₁ α
    comp-inv-left β α = comp₌-unitˡ α ∙
      (comp₌-cong (comp₌-inverseʳ β) (id₌ α) ∙ (comp₌-assoc β (β ⁻¹) α) ⁻¹)

    comp-inv-right : {C D : CAT Γ} {f g h : MAP C D}
      (α : g ＝ h) (β : f ＝ g)
      → ((α ∙ β) ∙ β ⁻¹) =₁ α
    comp-inv-right α β = comp₌-unitʳ α ∙
      (comp₌-cong (id₌ α) (comp₌-inverseʳ β) ∙ comp₌-assoc α β (β ⁻¹))

    inv-comp-right : {C D : CAT Γ} {f g h : MAP C D}
      (α : f ＝ h) (β : f ＝ g)
      → ((α ∙ β ⁻¹) ∙ β) =₁ α
    inv-comp-right α β = comp₌-unitʳ α ∙
      (comp₌-cong (id₌ α) (comp₌-inverseˡ β) ∙ comp₌-assoc α (β ⁻¹) β)

    reassociateFour : {C D : CAT Γ} {f g h i j : MAP C D}
      (δ : i ＝ j) (γ : h ＝ i) (β : g ＝ h) (α : f ＝ g)
      → ((δ ∙ γ) ∙ (β ∙ α)) =₁ (δ ∙ ((γ ∙ β) ∙ α))
    reassociateFour δ γ β α =
      comp₌-cong (id₌ δ) ((comp₌-assoc γ β α) ⁻¹) ∙ comp₌-assoc δ γ (β ∙ α)

```

## Part 3: naturality of unitors and associators

The naturality axioms state that prescribed squares of identification
families commute for universal inputs. Restricting them gives the same
prescribed squares for arbitrary families with a common parameter. The two
unitor laws restrict along the input family. The associator law restricts
along the left-nested triple of its inputs, matching its parameter category.
These proofs use horizontal coherence, not the vertical calculus.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    unitˡ-natural : {C D : CAT Γ} {f f′ : MAP C D} (α : f ＝ f′)
      → SquareCommutes (unitˡ-naturality-square α)
    unitˡ-natural {C = C} {D} {f} {f′} α =
      let source : ((const (comp-unitˡ f′) ∙ (const (id₌ (id D)) ⋆ id (Equal f f′))) ∘ α) =₁
                     (const (comp-unitˡ f′) ∙ (const (id₌ (id D)) ⋆ α))
          source = comp₌-evaluate-One (const (comp-unitˡ f′)) (const (id₌ (id D)) ⋆ id (Equal f f′)) α
            (const-pre (comp-unitˡ f′) α)
            (hcomp-evaluate-One (const (id₌ (id D))) (id (Equal f f′)) α
              (const-pre (id₌ (id D)) α) (comp-unitˡ α))
          target : ((id (Equal f f′) ∙ const (comp-unitˡ f)) ∘ α) =₁ (α ∙ const (comp-unitˡ f))
          target = comp₌-evaluate-One (id (Equal f f′)) (const (comp-unitˡ f)) α
            (comp-unitˡ α) (const-pre (comp-unitˡ f) α)
      in specialize (Coherence.unitˡ-natural f f′) α source target

    unitʳ-natural : {C D : CAT Γ} {f f′ : MAP C D} (α : f ＝ f′)
      → SquareCommutes (unitʳ-naturality-square α)
    unitʳ-natural {C = C} {D} {f} {f′} α =
      let source : ((const (comp-unitʳ f′) ∙ (id (Equal f f′) ⋆ const (id₌ (id C)))) ∘ α) =₁
                     (const (comp-unitʳ f′) ∙ (α ⋆ const (id₌ (id C))))
          source = comp₌-evaluate-One (const (comp-unitʳ f′)) (id (Equal f f′) ⋆ const (id₌ (id C))) α
            (const-pre (comp-unitʳ f′) α)
            (hcomp-evaluate-One (id (Equal f f′)) (const (id₌ (id C))) α
              (comp-unitˡ α) (const-pre (id₌ (id C)) α))
          target : ((id (Equal f f′) ∙ const (comp-unitʳ f)) ∘ α) =₁ (α ∙ const (comp-unitʳ f))
          target = comp₌-evaluate-One (id (Equal f f′)) (const (comp-unitʳ f)) α
            (comp-unitˡ α) (const-pre (comp-unitʳ f) α)
      in specialize (Coherence.unitʳ-natural f f′) α source target

    assoc-natural : {B C D E : CAT Γ}
      {f f′ : MAP B C} {g g′ : MAP C D} {h h′ : MAP D E}
      (γ : h ＝ h′) (β : g ＝ g′) (α : f ＝ f′)
      → SquareCommutes (associator-naturality-square γ β α)
    assoc-natural {f = f} {f′} {g} {g′} {h} {h′} γ β α =
      let open Triple γ β α
      in specialize (Coherence.assoc-natural f f′ g g′ h h′) triple
        (comp₌-evaluate-One (const (comp-assoc f′ g′ h′)) (((pr₁ ∘ pr₁) ⋆ (pr₂ ∘ pr₁)) ⋆ pr₂) triple
          (const-pre (comp-assoc f′ g′ h′) triple)
          (hcomp-evaluate-One ((pr₁ ∘ pr₁) ⋆ (pr₂ ∘ pr₁)) pr₂ triple
            (hcomp-evaluate-One (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) triple first second) third))
        (comp₌-evaluate-One ((pr₁ ∘ pr₁) ⋆ ((pr₂ ∘ pr₁) ⋆ pr₂)) (const (comp-assoc f g h)) triple
          (hcomp-evaluate-One (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ⋆ pr₂) triple first
            (hcomp-evaluate-One (pr₂ ∘ pr₁) pr₂ triple second third))
          (const-pre (comp-assoc f g h) triple))

```

Unfolded, `unitˡ-natural α` is the equation
`(const (comp-unitˡ f′) ∙ (const (id₌ (id D)) ⋆ α)) =₁ (α ∙ const (comp-unitˡ f))`,
and `assoc-natural γ β α` is
`(const (comp-assoc f′ g′ h′) ∙ ((γ ⋆ β) ⋆ α)) =₁ ((γ ⋆ (β ⋆ α)) ∙ const (comp-assoc f g h))`.

### Horizontal composition with identity identifications

A horizontal composite with a constant identity family on one side is the
corresponding whiskering. The left unit law of the vertical calculus removes
the whiskered identity, which whiskering preserves by `preWhisker-id₌` or
`postWhisker-id₌`. With identities on both sides one obtains the constant
identity family of the composite. These normalizations are shared by the
whiskering laws and by horizontal composition.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    hcomp-id-outer : {C D E : CAT Γ} {f f′ : MAP C D}
      (g : MAP D E) (α : f ＝ f′)
      → (const (id₌ g) ⋆ α) =₁ (g ◁ α)
    hcomp-id-outer {f′ = f′} g α = comp₌-unitˡ (g ◁ α) ∙
      comp₌-cong (const-cong (preWhisker-id₌ g f′) ∙ pre-constant (id₌ g) f′)
        (id₌ (g ◁ α))

    hcomp-id-inner : {C D E : CAT Γ} {g g′ : MAP D E}
      (β : g ＝ g′) (f : MAP C D)
      → (β ⋆ const (id₌ f)) =₁ (β ▷ f)
    hcomp-id-inner {g = g} β f = comp₌-unitʳ (β ▷ f) ∙
      comp₌-cong (id₌ (β ▷ f))
        (const-cong (postWhisker-id₌ g f) ∙ post-constant g (id₌ f))

  hcomp-id₌ : {X C D E : CAT Γ} (g : MAP D E) (f : MAP C D)
    → (const {P = X} (id₌ g) ⋆ const (id₌ f)) =₁ (const (id₌ (g ∘ f)))
  hcomp-id₌ g f = const-cong (postWhisker-id₌ g f) ∙
    (post-constant g (id₌ f) ∙ hcomp-id-outer g (const (id₌ f)))

```

## Part 4: whiskering and interchange

Whiskering preserves vertical composition, and the joint interchange law
compares the two orders of whiskering two families. Each universal law is
restricted along the pair of its input families. These proofs use only the
primitive whiskering and interchange axioms.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    postWhisker-comp₌ : {C D E : CAT Γ} {f g h : MAP C D}
      (u : MAP D E) (τ : g ＝ h) (σ : f ＝ g)
      → (u ◁ (τ ∙ σ)) =₁ ((u ◁ τ) ∙ (u ◁ σ))
    postWhisker-comp₌ {f = f} {g} {h} u τ σ =
      let parameters = pair τ σ
      in specialize (Coherence.postWhisker-comp₌ f g h u) parameters
        (postWhisker-evaluate-One u (pr₁ ∙ pr₂) parameters
          (comp₌-evaluate-One pr₁ pr₂ parameters (pair-β₁ τ σ) (pair-β₂ τ σ)))
        (comp₌-evaluate-One (u ◁ pr₁) (u ◁ pr₂) parameters
          (postWhisker-evaluate-One u pr₁ parameters (pair-β₁ τ σ))
          (postWhisker-evaluate-One u pr₂ parameters (pair-β₂ τ σ)))

    preWhisker-comp₌ : {B C D : CAT Γ} {f g h : MAP C D}
      (τ : g ＝ h) (σ : f ＝ g) (k : MAP B C)
      → ((τ ∙ σ) ▷ k) =₁ ((τ ▷ k) ∙ (σ ▷ k))
    preWhisker-comp₌ {f = f} {g} {h} τ σ k =
      let parameters = pair τ σ
      in specialize (Coherence.preWhisker-comp₌ f g h k) parameters
        (preWhisker-evaluate-One (pr₁ ∙ pr₂) k parameters
          (comp₌-evaluate-One pr₁ pr₂ parameters (pair-β₁ τ σ) (pair-β₂ τ σ)))
        (comp₌-evaluate-One (pr₁ ▷ k) (pr₂ ▷ k) parameters
          (preWhisker-evaluate-One pr₁ k parameters (pair-β₁ τ σ))
          (preWhisker-evaluate-One pr₂ k parameters (pair-β₂ τ σ)))

    interchange : {B C D : CAT Γ} {F G : MAP C D} {h k : MAP B C}
      (τ : F ＝ G) (σ : h ＝ k)
      → ((τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ (τ ▷ h))
    interchange {F = F} {G} {h} {k} τ σ =
      let parameters = pair τ σ
      in specialize (Coherence.interchange F G h k) parameters
        (comp₌-evaluate-One (pr₁ ▷ k) (F ◁ pr₂) parameters
          (preWhisker-evaluate-One pr₁ k parameters (pair-β₁ τ σ))
          (postWhisker-evaluate-One F pr₂ parameters (pair-β₂ τ σ)))
        (comp₌-evaluate-One (G ◁ pr₂) (pr₁ ▷ h) parameters
          (postWhisker-evaluate-One G pr₂ parameters (pair-β₂ τ σ))
          (preWhisker-evaluate-One pr₁ h parameters (pair-β₁ τ σ)))
```

### Interchange with one fixed input

When one input is a fixed identification, insert its constant family into
the family interchange law. Whiskering a constant family is the constant
family of the whiskering, so both sides normalize to the following mixed
statements: one input is an individual identification, the other a family.

```agda
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    interchange-fixedOuter : {B C D : CAT Γ} {F G : MAP C D} {h k : MAP B C}
      (τ : F =₁ G) (σ : h ＝ k)
      → (const (τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ const (τ ▷ h))
    interchange-fixedOuter {F = F} {G} {h} {k} τ σ =
      comp₌-cong (id₌ (G ◁ σ)) (pre-constant τ h) ∙
        (interchange (const τ) σ ∙
          (comp₌-cong (pre-constant τ k) (id₌ (F ◁ σ))) ⁻¹)

    interchange-fixedInner : {B C D : CAT Γ} {F G : MAP C D} {h k : MAP B C}
      (τ : F ＝ G) (σ : h =₁ k)
      → ((τ ▷ k) ∙ const (F ◁ σ)) =₁ (const (G ◁ σ) ∙ (τ ▷ h))
    interchange-fixedInner {F = F} {G} {h} {k} τ σ =
      comp₌-cong (post-constant G σ) (id₌ (τ ▷ h)) ∙
        (interchange τ (const σ) ∙
          (comp₌-cong (id₌ (τ ▷ k)) (post-constant F σ)) ⁻¹)
```
