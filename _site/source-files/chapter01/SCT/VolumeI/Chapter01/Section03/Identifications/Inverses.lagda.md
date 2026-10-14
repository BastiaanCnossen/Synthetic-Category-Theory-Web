# Inverses and cancellation of identifications

Every later calculation with identifications uses the inverse laws in a few
standard forms: cancelling an inverse pair next to another identification,
cancelling a common factor from an equation, recognizing a specified inverse
by its inverse law, and computing inverses of composites and of whiskerings.
The four reductions of an inverse pair are in Specialization; this module
derives the remaining tools. All statements are for identification families
with an arbitrary common parameter, except the four normalizations at `One`
in the first section and the inverse of an identity identification, which
concern fixed identity identifications.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.Inverses where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; inv₌; comp₌; comp-unitˡ; comp-unitʳ; comp-assoc;
    postWhisker-id₌; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
```

## Unit and inverse laws at One

For individual identifications the family unit and inverse laws have constant
identity families as boundaries. `const-One` identifies these with the
identity identifications themselves. These four normalizations are shared,
since many calculations with fixed specified identifications need them.

```agda
module _ {Γ : Context} where
  module _ {C : CAT Γ} where
    open Terms.InContext C using (Term)

    comp₌-unitˡ-One : {D : CAT Γ} {x y : Term D} (α : x =₁ y) → (id₌ y ∙ α) =₂ α
    comp₌-unitˡ-One {y = y} α =
      comp₌-unitˡ α ∙ comp₌-cong ((const-One (id₌ y)) ⁻¹) (id₌ α)

    comp₌-unitʳ-One : {D : CAT Γ} {x y : Term D} (α : x =₁ y) → (α ∙ id₌ x) =₂ α
    comp₌-unitʳ-One {x = x} α =
      comp₌-unitʳ α ∙ comp₌-cong (id₌ α) ((const-One (id₌ x)) ⁻¹)

    comp₌-inverseˡ-One : {D : CAT Γ} {x y : Term D} (α : x =₁ y) → (α ⁻¹ ∙ α) =₂ id₌ x
    comp₌-inverseˡ-One {x = x} α = const-One (id₌ x) ∙ comp₌-inverseˡ α

    comp₌-inverseʳ-One : {D : CAT Γ} {x y : Term D} (α : x =₁ y) → (α ∙ α ⁻¹) =₂ id₌ y
    comp₌-inverseʳ-One {y = y} α = const-One (id₌ y) ∙ comp₌-inverseʳ α
```

## Cancelling a common factor

An equation between two composites with a common first or last factor
remains true after removing that factor: compose with its inverse and apply
an inverse reduction on both sides.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    cancel-left : {D : CAT Γ} {x y z : Term D}
      (β : y ＝ z) {α α′ : x ＝ y}
      → (β ∙ α) =₁ (β ∙ α′) → α =₁ α′
    cancel-left β {α} {α′} p =
      inv-comp-left β α′ ∙ (comp₌-cong (id₌ (β ⁻¹)) p ∙ (inv-comp-left β α) ⁻¹)

    cancel-right : {D : CAT Γ} {x y z : Term D}
      (β : x ＝ y) {α α′ : y ＝ z}
      → (α ∙ β) =₁ (α′ ∙ β) → α =₁ α′
    cancel-right β {α} {α′} p =
      comp-inv-right α′ β ∙ (comp₌-cong p (id₌ (β ⁻¹)) ∙ (comp-inv-right α β) ⁻¹)
```

## Inverses

A left inverse of `α` is its specified inverse: both satisfy the left inverse
law, so cancel `α`. Consequently inversion is involutive, reverses composites,
and commutes with whiskering, which preserves identity identifications and
vertical composites.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    inverse-unique : {D : CAT Γ} {x y : Term D}
      (α : x ＝ y) (β : y ＝ x)
      → (β ∙ α) =₁ const (id₌ x) → (α ⁻¹) =₁ β
    inverse-unique α β p = cancel-right α (p ⁻¹ ∙ comp₌-inverseˡ α)

  inverse-identity : {C D : CAT Γ} (f : MAP C D) → ((id₌ f) ⁻¹) =₂ (id₌ f)
  inverse-identity f =
    inverse-unique (id₌ f) (id₌ f) ((const-One (id₌ f)) ⁻¹ ∙ comp₌-unitˡ-One (id₌ f))

  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    inverse-inverse : {D : CAT Γ} {x y : Term D} (α : x ＝ y)
      → ((α ⁻¹) ⁻¹) =₁ α
    inverse-inverse α = inverse-unique (α ⁻¹) α (comp₌-inverseʳ α)

    inverse-composite : {D : CAT Γ} {x y z : Term D}
      (β : y ＝ z) (α : x ＝ y)
      → ((β ∙ α) ⁻¹) =₁ (α ⁻¹ ∙ β ⁻¹)
    inverse-composite β α = inverse-unique (β ∙ α) (α ⁻¹ ∙ β ⁻¹)
      (comp₌-inverseˡ α ∙
        (comp₌-cong (id₌ (α ⁻¹)) (inv-comp-left β α) ∙
          comp₌-assoc (α ⁻¹) (β ⁻¹) (β ∙ α)))

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    postWhisker-inverse : {B C D : CAT Γ} (F : MAP C D) {u v : MAP B C}
      (α : u ＝ v) → (F ◁ α ⁻¹) =₁ ((F ◁ α) ⁻¹)
    postWhisker-inverse F {u} α = cancel-right (F ◁ α)
      ((comp₌-inverseˡ (F ◁ α)) ⁻¹ ∙
        (const-cong (postWhisker-id₌ F u) ∙
          (post-constant F (id₌ u) ∙
            ((postWhisker F ◁ comp₌-inverseˡ α) ∙ (postWhisker-comp₌ F (α ⁻¹) α) ⁻¹))))

  module _ {X B C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    preWhisker-inverse : {D : CAT Γ} {u v : Term D}
      (α : u ＝ v) (r : MAP B C) → (α ⁻¹ ▷ r) =₁ ((α ▷ r) ⁻¹)
    preWhisker-inverse {u = u} α r = cancel-right (α ▷ r)
      ((comp₌-inverseˡ (α ▷ r)) ⁻¹ ∙
        (const-cong (preWhisker-id₌ u r) ∙
          (pre-constant (id₌ u) r ∙
            ((preWhisker r ◁ comp₌-inverseˡ α) ∙ (preWhisker-comp₌ (α ⁻¹) α r) ⁻¹))))
```

## Solving composite equations

The composite of two identifications followed by their inverses in reversed
order is an identity. A commuting pentagon, written as in `PentagonCommutes`
with a two-factor source route and a left-associated three-factor target
route, can be solved for one corner, in either of the two orientations used
by later calculations.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    inverse-tail : {D : CAT Γ} {x y z : Term D}
      (β : y ＝ z) (α : x ＝ y)
      → ((β ∙ α) ∙ (α ⁻¹ ∙ β ⁻¹)) =₁ const (id₌ z)
    inverse-tail β α = comp₌-inverseʳ β ∙
      (comp₌-cong (id₌ β)
        (comp₌-unitˡ (β ⁻¹) ∙ comp₌-cong (comp₌-inverseʳ α) (id₌ (β ⁻¹))) ∙
        reassociateFour β α (α ⁻¹) (β ⁻¹))

    solve-pentagon : {D : CAT Γ} {x₀ x₁ x₂ x₃ x₄ : Term D}
      (A : x₁ ＝ x₄) (B : x₀ ＝ x₁)
      (C′ : x₃ ＝ x₄) (D′ : x₂ ＝ x₃) (E : x₀ ＝ x₂)
      → (A ∙ B) =₁ ((C′ ∙ D′) ∙ E)
      → (B ∙ (E ⁻¹ ∙ D′ ⁻¹)) =₁ (A ⁻¹ ∙ C′)
    solve-pentagon A B C′ D′ E pentagon =
      let p = comp₌-assoc C′ D′ E ∙ pentagon
          tail = E ⁻¹ ∙ D′ ⁻¹
          cleared : (A ∙ (B ∙ tail)) =₁ C′
          cleared = comp₌-unitʳ C′ ∙
            (comp₌-cong (id₌ C′) (inverse-tail D′ E) ∙
              (comp₌-assoc C′ (D′ ∙ E) tail ∙
                (comp₌-cong p (id₌ tail) ∙ (comp₌-assoc A B tail) ⁻¹)))
      in cancel-left A ((comp-inv-left A C′) ⁻¹ ∙ cleared)

    pentagon-left-corner : {D : CAT Γ} {x₀ x₁ x₂ x₃ x₄ : Term D}
      (A : x₁ ＝ x₄) (B : x₀ ＝ x₁)
      (C′ : x₃ ＝ x₄) (D′ : x₂ ＝ x₃) (E : x₀ ＝ x₂)
      → (A ∙ B) =₁ ((C′ ∙ D′) ∙ E)
      → (D′ ⁻¹ ∙ (C′ ⁻¹ ∙ A)) =₁ (E ∙ B ⁻¹)
    pentagon-left-corner A B C′ D′ E pentagon =
      let p = comp₌-assoc C′ D′ E ∙ pentagon
          expand-corner : A =₁ (C′ ∙ (D′ ∙ (E ∙ B ⁻¹)))
          expand-corner = comp₌-cong (id₌ C′) (comp₌-assoc D′ E (B ⁻¹)) ∙
            (comp₌-assoc C′ (D′ ∙ E) (B ⁻¹) ∙
              (comp₌-cong p (id₌ (B ⁻¹)) ∙ (comp-inv-right A B) ⁻¹))
      in inv-comp-left D′ (E ∙ B ⁻¹) ∙
        (comp₌-cong (id₌ (D′ ⁻¹)) (inv-comp-left C′ (D′ ∙ (E ∙ B ⁻¹))) ∙
          comp₌-cong (id₌ (D′ ⁻¹)) (comp₌-cong (id₌ (C′ ⁻¹)) expand-corner))
```

## Reassociation and cancellation with a tail

These are finite combinations of associativity and the inverse reductions,
with the bracketings used by restriction and cone calculations.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    comp₌-prefix-assoc : {D : CAT Γ} {x₀ x₁ x₂ x₃ f₄ : Term D}
      (a₃ : x₃ ＝ f₄) (a₂ : x₂ ＝ x₃)
      (a₁ : x₁ ＝ x₂) (a₀ : x₀ ＝ x₁)
      → (a₃ ∙ (a₂ ∙ (a₁ ∙ a₀))) =₁ ((a₃ ∙ (a₂ ∙ a₁)) ∙ a₀)
    comp₌-prefix-assoc a₃ a₂ a₁ a₀ = (comp₌-assoc a₃ (a₂ ∙ a₁) a₀) ⁻¹ ∙
      comp₌-cong (id₌ a₃) ((comp₌-assoc a₂ a₁ a₀) ⁻¹)

    cancel-inverse-with-tail : {D : CAT Γ} {a b c d e : Term D}
      (W : c ＝ d) (v : e ＝ d) (E : b ＝ e) (η : a ＝ b)
      → (W ∙ ((W ⁻¹ ∙ (v ∙ E)) ∙ η)) =₁ (v ∙ (E ∙ η))
    cancel-inverse-with-tail W v E η = comp₌-assoc v E η ∙
      (comp₌-cong (comp-inv-left W (v ∙ E)) (id₌ η) ∙
        (comp₌-assoc W (W ⁻¹ ∙ (v ∙ E)) η) ⁻¹)

    cancel-right-two : {D : CAT Γ} {a b c d : Term D}
      (α : c ＝ d) (β : b ＝ c) (γ : a ＝ b)
      → (((α ∙ (β ∙ γ)) ∙ γ ⁻¹) ∙ β ⁻¹) =₁ α
    cancel-right-two α β γ = comp-inv-right α β ∙
      (comp₌-cong (comp-inv-right (α ∙ β) γ) (id₌ (β ⁻¹)) ∙
        comp₌-cong (comp₌-cong ((comp₌-assoc α β γ) ⁻¹) (id₌ (γ ⁻¹))) (id₌ (β ⁻¹)))

    cancel-two-inverses : {D : CAT Γ} {f y z w : Term D}
      (b : z ＝ w) (a : y ＝ z) (x : f ＝ w)
      → ((b ∙ a) ∙ (a ⁻¹ ∙ (b ⁻¹ ∙ x))) =₁ x
    cancel-two-inverses b a x = comp-inv-left b x ∙
      (comp₌-cong (id₌ b) (comp-inv-left a (b ⁻¹ ∙ x)) ∙
        comp₌-assoc b a (a ⁻¹ ∙ (b ⁻¹ ∙ x)))
```
