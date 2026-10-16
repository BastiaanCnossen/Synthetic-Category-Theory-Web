# Squares of identifications

A square of identification families has a top edge `t : f = g`, a bottom
edge `b : f′ = g′` and sides `l : f = f′`, `r : g = g′`, all families with a
common parameter. It commutes when `SquareCell₌ t b l r`, that is
`r ∙ t =₁ b ∙ l` (Section02.Coherence). These squares are distinct from the
squares between functors of Section03.Squares, whose edges are functors.

This module provides the operations on commuting squares used throughout the
identification calculus: the identity square, the two pastings (along a
common horizontal edge, and along a common side), transposition, inversion,
whiskering by functors, horizontal composition with an identification,
replacement of edges along identifications, and the filling of a cube from
five of its faces. Sides that are fixed
identifications appear as constant families; one adapter converts constant
sides at the parameter `One` into the identifications themselves.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section02.IdentificationSquares where

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
open import SCT.VolumeI.Chapter01.Section02.Specialization
```

## Identity, pasting and transposition

The identity square has an identification as top and bottom edge and constant
identity families as sides. Pasting along a common horizontal edge composes
the sides; pasting along a common side composes the horizontal edges.
Transposing exchanges the roles of edges and sides and reverses the filler.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    identity-square₌ : {D : CAT Γ} {x y : Term D} (α : x ＝ y)
      → SquareCell₌ α α (const (id₌ x)) (const (id₌ y))
    identity-square₌ α = (comp₌-unitʳ α) ⁻¹ ∙ comp₌-unitˡ α

    paste-square₌ : {D : CAT Γ} {x y x′ y′ x″ y″ : Term D}
      {t : x ＝ y} {m : x′ ＝ y′} {b : x″ ＝ y″}
      {l₁ : x ＝ x′} {r₁ : y ＝ y′}
      {l₂ : x′ ＝ x″} {r₂ : y′ ＝ y″}
      → SquareCell₌ t m l₁ r₁ → SquareCell₌ m b l₂ r₂
      → SquareCell₌ t b (l₂ ∙ l₁) (r₂ ∙ r₁)
    paste-square₌ {t = t} {m} {b} {l₁} {r₁} {l₂} {r₂} upper lower =
      comp₌-assoc b l₂ l₁ ∙
        (comp₌-cong lower (id₌ l₁) ∙
          ((comp₌-assoc r₂ m l₁) ⁻¹ ∙
            (comp₌-cong (id₌ r₂) upper ∙ comp₌-assoc r₂ r₁ t)))

    adjoin-square₌ : {D : CAT Γ} {x y z x′ y′ z′ : Term D}
      {t₁ : x ＝ y} {b₁ : x′ ＝ y′}
      {t₂ : y ＝ z} {b₂ : y′ ＝ z′}
      {l : x ＝ x′} {m : y ＝ y′} {r : z ＝ z′}
      → SquareCell₌ t₁ b₁ l m → SquareCell₌ t₂ b₂ m r
      → SquareCell₌ (t₂ ∙ t₁) (b₂ ∙ b₁) l r
    adjoin-square₌ {t₁ = t₁} {b₁} {t₂} {b₂} {l} {m} {r} first second =
      (comp₌-assoc b₂ b₁ l) ⁻¹ ∙
        (comp₌-cong (id₌ b₂) first ∙
          (comp₌-assoc b₂ m t₁ ∙
            (comp₌-cong second (id₌ t₁) ∙ (comp₌-assoc r t₂ t₁) ⁻¹)))

    transpose-square₌ : {D : CAT Γ} {x y x′ y′ : Term D}
      {t : x ＝ y} {b : x′ ＝ y′}
      {l : x ＝ x′} {r : y ＝ y′}
      → SquareCell₌ t b l r → SquareCell₌ l r t b
    transpose-square₌ square = square ⁻¹
```

## Inverting a square

Reversing the vertical direction of a square exchanges top and bottom and
inverts both sides. Combined with transposition, it inverts the horizontal
edges instead. Pasting a square with such an inverted square along their
common target gives the square of the composite `β ⁻¹ ∙ α`.

```agda
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    inverse-square₌ : {D : CAT Γ} {x y x′ y′ : Term D}
      {t : x ＝ y} {b : x′ ＝ y′}
      {l : x ＝ x′} {r : y ＝ y′}
      → SquareCell₌ t b l r → SquareCell₌ b t (l ⁻¹) (r ⁻¹)
    inverse-square₌ {t = t} {b} {l} {r} square =
      let rearranged : t =₁ ((r ⁻¹ ∙ b) ∙ l)
          rearranged = (comp₌-assoc (r ⁻¹) b l) ⁻¹ ∙
            (comp₌-cong (id₌ (r ⁻¹)) square ∙ (inv-comp-left r t) ⁻¹)
      in (comp-inv-right (r ⁻¹ ∙ b) l ∙ comp₌-cong rearranged (id₌ (l ⁻¹))) ⁻¹

    inv-comp-square₌ : {D : CAT Γ} {x y z x′ y′ z′ : Term D}
      {α : x ＝ z} {β : y ＝ z}
      {α′ : x′ ＝ z′} {β′ : y′ ＝ z′}
      {L : x ＝ x′} {R : y ＝ y′} {V : z ＝ z′}
      → SquareCell₌ α α′ L V → SquareCell₌ β β′ R V
      → SquareCell₌ (β ⁻¹ ∙ α) (β′ ⁻¹ ∙ α′) L R
    inv-comp-square₌ left right = adjoin-square₌ left
      (transpose-square₌ (inverse-square₌ (transpose-square₌ right)))
```

## Whiskering and horizontal composition

Whiskering by a functor preserves vertical composites, hence carries a
commuting square to a commuting square. Horizontal composition with a fixed
family, on either side, does the same; there the sides become whiskerings.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    post-square₌ : {B C D : CAT Γ} (F : MAP C D) {f g f′ g′ : MAP B C}
      {t : f ＝ g} {b : f′ ＝ g′}
      {l : f ＝ f′} {r : g ＝ g′}
      → SquareCell₌ t b l r → SquareCell₌ (F ◁ t) (F ◁ b) (F ◁ l) (F ◁ r)
    post-square₌ F {t = t} {b} {l} {r} square = postWhisker-comp₌ F b l ∙
      ((postWhisker F ◁ square) ∙ (postWhisker-comp₌ F r t) ⁻¹)

  module _ {X B C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    pre-square₌ : {D : CAT Γ} (k : MAP B C) {x y x′ y′ : Term D}
      {t : x ＝ y} {b : x′ ＝ y′}
      {l : x ＝ x′} {r : y ＝ y′}
      → SquareCell₌ t b l r → SquareCell₌ (t ▷ k) (b ▷ k) (l ▷ k) (r ▷ k)
    pre-square₌ k {t = t} {b} {l} {r} square = preWhisker-comp₌ b l k ∙
      ((preWhisker k ◁ square) ∙ (preWhisker-comp₌ r t k) ⁻¹)

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    hcomp-square₌-outer : {A B C : CAT Γ} {f f′ : MAP A B}
      {g g′ G G′ : MAP B C}
      {α : g ＝ g′} {δ : G ＝ G′}
      {p : g ＝ G} {q : g′ ＝ G′}
      → SquareCell₌ α δ p q → (β : f ＝ f′)
      → SquareCell₌ (α ⋆ β) (δ ⋆ β) (p ▷ f) (q ▷ f′)
    hcomp-square₌-outer {f = f} {f′} {g} {g′} {G} {G′} {α} {δ} {p} {q} square β =
      (comp₌-assoc (δ ▷ f′) (G ◁ β) (p ▷ f)) ⁻¹ ∙
      (comp₌-cong (id₌ (δ ▷ f′)) (interchange p β) ∙
      (comp₌-assoc (δ ▷ f′) (p ▷ f′) (g ◁ β) ∙
      (comp₌-cong (preWhisker-comp₌ δ p f′) (id₌ (g ◁ β)) ∙
      (comp₌-cong (preWhisker f′ ◁ square) (id₌ (g ◁ β)) ∙
      (comp₌-cong ((preWhisker-comp₌ q α f′) ⁻¹) (id₌ (g ◁ β)) ∙
        (comp₌-assoc (q ▷ f′) (α ▷ f′) (g ◁ β)) ⁻¹)))))

    hcomp-square₌-inner : {A B C : CAT Γ} {f f′ F F′ : MAP A B}
      {g g′ : MAP B C}
      {α : f ＝ f′} {δ : F ＝ F′}
      {p : f ＝ F} {q : f′ ＝ F′}
      → SquareCell₌ α δ p q → (β : g ＝ g′)
      → SquareCell₌ (β ⋆ α) (β ⋆ δ) (g ◁ p) (g′ ◁ q)
    hcomp-square₌-inner {f = f} {f′} {F} {F′} {g} {g′} {α} {δ} {p} {q} square β =
      (comp₌-assoc (β ▷ F′) (g ◁ δ) (g ◁ p)) ⁻¹ ∙
      (comp₌-cong (id₌ (β ▷ F′)) (postWhisker-comp₌ g δ p) ∙
      (comp₌-cong (id₌ (β ▷ F′)) (postWhisker g ◁ square) ∙
      (comp₌-cong (id₌ (β ▷ F′)) ((postWhisker-comp₌ g q α) ⁻¹) ∙
      (comp₌-assoc (β ▷ F′) (g ◁ q) (g ◁ α) ∙
      (comp₌-cong ((interchange β q) ⁻¹) (id₌ (g ◁ α)) ∙
        (comp₌-assoc (g′ ◁ q) (β ▷ f′) (g ◁ α)) ⁻¹)))))
```

## Replacing edges and constant squares

A square remains commuting when its edges are replaced along given
identifications of families. A commuting square of individual
identifications gives a commuting square of their constant families over any
parameter. At the parameter `One`, constant sides are identified with the
underlying identifications by `const-One`; this is the single adapter between
family statements with fixed sides and their individual instances.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    replace-sides₌ : {D : CAT Γ} {x y x′ y′ : Term D}
      {t : x ＝ y} {b : x′ ＝ y′}
      {l l′ : x ＝ x′} {r r′ : y ＝ y′}
      → l =₁ l′ → r =₁ r′ → SquareCell₌ t b l r → SquareCell₌ t b l′ r′
    replace-sides₌ {t = t} {b} change-left change-right square =
      comp₌-cong (id₌ b) change-left ∙ (square ∙ comp₌-cong (change-right ⁻¹) (id₌ t))

    replace-edges₌ : {D : CAT Γ} {x y x′ y′ : Term D}
      {t t′ : x ＝ y} {b b′ : x′ ＝ y′}
      {l : x ＝ x′} {r : y ＝ y′}
      → t =₁ t′ → b =₁ b′ → SquareCell₌ t b l r → SquareCell₌ t′ b′ l r
    replace-edges₌ {l = l} {r} change-top change-bottom square =
      comp₌-cong change-bottom (id₌ l) ∙ (square ∙ comp₌-cong (id₌ r) (change-top ⁻¹))

  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)

    constant-square₌ : {D : CAT Γ} {x y x′ y′ : Term D}
      {t : x =₁ y} {b : x′ =₁ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b l r
      → SquareCell₌ {X = X} (const t) (const b) (const l) (const r)
    constant-square₌  {t = t} {b} {l} {r} square =
      (const-comp {X = X} b l) ⁻¹ ∙ (const-cong square ∙ const-comp {X = X} r t)

  module _ {C : CAT Γ} where
    open Terms.InContext C using (Term)

    unconst-sides₌ : {D : CAT Γ} {x y x′ y′ : Term D}
      {t : x =₁ y} {b : x′ =₁ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b (const l) (const r) → SquareCell₌ t b l r
    unconst-sides₌ {l = l} {r} = replace-sides₌ (const-One l) (const-One r)

    const-sides₌ : {D : CAT Γ} {x y x′ y′ : Term D}
      {t : x =₁ y} {b : x′ =₁ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b l r → SquareCell₌ t b (const l) (const r)
    const-sides₌ {l = l} {r} = replace-sides₌ ((const-One l) ⁻¹) ((const-One r) ⁻¹)
```

## Whiskered composites

Whiskering a vertical composite next to a further identification splits it
into two whiskered factors. The postwhiskered case with a trailing
identification is the computation used to project a pasted edge.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    project-composite : {Y K C : CAT Γ} {h₀ h₁ h₂ : MAP Y K} {z : MAP Y C}
      (π : MAP K C) (β : h₁ ＝ h₂) (α : h₀ ＝ h₁)
      (b : ((π ∘ h₂) ＝ z))
      → (b ∙ (π ◁ (β ∙ α))) =₁ ((b ∙ (π ◁ β)) ∙ (π ◁ α))
    project-composite π β α b = (comp₌-assoc b (π ◁ β) (π ◁ α)) ⁻¹ ∙
      comp₌-cong (id₌ b) (postWhisker-comp₌ π β α)

    postwhiskered-composite : {A B C : CAT Γ} {a b c : MAP A B} {x : MAP A C}
      (k : MAP B C) (α : b ＝ c) (β : a ＝ b) (γ : (x ＝ (k ∘ a)))
      → ((k ◁ (α ∙ β)) ∙ γ) =₁ ((k ◁ α) ∙ ((k ◁ β) ∙ γ))
    postwhiskered-composite k α β γ = comp₌-assoc (k ◁ α) (k ◁ β) γ ∙
      comp₌-cong (postWhisker-comp₌ k α β) (id₌ γ)

  module _ {X B C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    prewhiskered-composite : {D : CAT Γ} {a b c : Term D} {x : MAP B D}
      (k : MAP B C) (α : b ＝ c) (β : a ＝ b) (γ : (x ＝ (a ∘ k)))
      → (((α ∙ β) ▷ k) ∙ γ) =₁ ((α ▷ k) ∙ ((β ▷ k) ∙ γ))
    prewhiskered-composite k α β γ = comp₌-assoc (α ▷ k) (β ▷ k) γ ∙
      comp₌-cong (preWhisker-comp₌ α β k) (id₌ γ)
```

## Cubes

A cube of identifications has an upper square with top edge `t`, bottom
edge `k` and sides `l`, `r`, a lower square of the same shape with primed
edges, and vertical edges `va`, `vb`, `vc`, `vd` joining corresponding
vertices. If the upper, lower, left, right and back faces commute, so does
the front face: pasting the upper face with the back face gives a square
whose sides are those of the left and right faces, and cancelling the lower
face leaves the front face. All twelve edges are determined by the faces.

```agda
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    fill-cube₌ : {D : CAT Γ} {a b c d a′ b′ c′ d′ : Term D}
      {t : a ＝ d} {k : b ＝ c} {l : a ＝ b} {r : d ＝ c}
      {t′ : a′ ＝ d′} {k′ : b′ ＝ c′} {l′ : a′ ＝ b′} {r′ : d′ ＝ c′}
      {va : a ＝ a′} {vb : b ＝ b′} {vc : c ＝ c′} {vd : d ＝ d′}
      → (upper : SquareCell₌ t k l r) (lower : SquareCell₌ t′ k′ l′ r′)
      → (left : SquareCell₌ l l′ va vb) (right : SquareCell₌ r r′ vd vc)
      → (back : SquareCell₌ vb vc k k′)
      → SquareCell₌ t t′ va vd
    fill-cube₌ {t = t} {k} {l} {r} {t′} {k′} {l′} {r′} {va} {vb} {vc} {vd}
      upper lower left right back =
      replace-sides₌ (inv-comp-left l′ va) (inv-comp-left r′ vd)
        (paste-square₌ {t = t} {m = k′} {b = t′}
          (replace-sides₌ left right
            (paste-square₌ {t = t} {m = k} {b = k′} upper (transpose-square₌ back)))
          (inverse-square₌ lower))
```
