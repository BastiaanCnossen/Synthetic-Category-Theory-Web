# Changing the endpoints of identifications

Given `p : f = f′` and `q : g = g′`, an identification `α : f = g` becomes
`q ∙ (α ∙ p ⁻¹) : f′ = g′`. This is the common bracketing for endpoint
change. The file has five parts:

1. The operation on families and its basic laws: congruence, composition,
   identity, iteration, reflection, and its relation to commuting squares.
2. The functor `changeEndpoints₌ p q` between identification animae, an
   equivalence, and its evaluation at a family.
3. Transport of finite diagrams: changing the vertices of a commuting
   triangle or pentagon (as in Section02.Coherence), or replacing edges with
   fixed vertices.
4. Transport of squares, and the cancellations used when encoding and
   decoding endpoint changes.
5. Restriction of specified identifications along a functor.

The diagram transports carry a *supplied* commuting diagram along vertex
changes; they do not assert new coherence. The operation needs no mapping
anima structure.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; inv₌; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (preWhisker-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (postcomp₌; precomp₌; postcomp₌-isEquiv; precomp₌-isEquiv;
    postcomp₌-evaluate; precomp₌-evaluate)
```

## Part 1: the operation

All laws are stated for families with a common parameter. Reflection does
not need the equivalence below: it cancels the two endpoint factors.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    changeEndpoints : {D : CAT Γ} {x x′ y y′ : Term D}
      → (x ＝ x′) → (y ＝ y′) → (x ＝ y) → (x′ ＝ y′)
    changeEndpoints p q α = q ∙ (α ∙ p ⁻¹)

    changeEndpoints-cong : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x ＝ x′) (q : y ＝ y′) {α β : x ＝ y}
      → α =₁ β → changeEndpoints p q α =₁ changeEndpoints p q β
    changeEndpoints-cong p q c = comp₌-cong (id₌ q) (comp₌-cong c (id₌ (p ⁻¹)))

    changeEndpoints-comp : {D : CAT Γ} {x x′ y y′ z z′ : Term D}
      (p : x ＝ x′) (q : y ＝ y′) (r : z ＝ z′)
      (β : y ＝ z) (α : x ＝ y)
      → (changeEndpoints q r β ∙ changeEndpoints p q α) =₁ changeEndpoints p r (β ∙ α)
    changeEndpoints-comp p q r β α =
      let remaining = α ∙ p ⁻¹
          cancel : ((β ∙ q ⁻¹) ∙ (q ∙ remaining)) =₁ (β ∙ remaining)
          cancel = comp₌-cong (id₌ β) (inv-comp-left q remaining) ∙
            comp₌-assoc β (q ⁻¹) (q ∙ remaining)
      in comp₌-cong (id₌ r) ((comp₌-assoc β α (p ⁻¹)) ⁻¹ ∙ cancel) ∙
        comp₌-assoc r (β ∙ q ⁻¹) (q ∙ remaining)

    changeEndpoints-id : {D : CAT Γ} {x y : Term D} (p : x ＝ y)
      → changeEndpoints p p (const (id₌ x)) =₁ const (id₌ y)
    changeEndpoints-id p = comp₌-inverseʳ p ∙ comp₌-cong (id₌ p) (comp₌-unitˡ (p ⁻¹))

    changeEndpoints-comp₃ : {D : CAT Γ} {x x′ y y′ z z′ w w′ : Term D}
      (p : x ＝ x′) (q : y ＝ y′) (r : z ＝ z′) (s : w ＝ w′)
      (γ : z ＝ w) (β : y ＝ z) (α : x ＝ y)
      → ((changeEndpoints r s γ ∙ changeEndpoints q r β) ∙ changeEndpoints p q α) =₁
          changeEndpoints p s ((γ ∙ β) ∙ α)
    changeEndpoints-comp₃ p q r s γ β α = changeEndpoints-comp p q s (γ ∙ β) α ∙
      comp₌-cong (changeEndpoints-comp q r s γ β) (id₌ (changeEndpoints p q α))

    changeEndpoints-iterated : {D : CAT Γ} {u v u′ v′ u″ v″ : Term D}
      (p : u ＝ u′) (q : v ＝ v′)
      (p′ : u′ ＝ u″) (q′ : v′ ＝ v″) (α : u ＝ v)
      → changeEndpoints p′ q′ (changeEndpoints p q α) =₁ changeEndpoints (p′ ∙ p) (q′ ∙ q) α
    changeEndpoints-iterated p q p′ q′ α = comp₌-cong (id₌ (q′ ∙ q))
        (comp₌-cong (id₌ α) ((inverse-composite p′ p) ⁻¹) ∙ comp₌-assoc α (p ⁻¹) (p′ ⁻¹)) ∙
      ((comp₌-assoc q′ q ((α ∙ p ⁻¹) ∙ p′ ⁻¹)) ⁻¹ ∙
        comp₌-cong (id₌ q′) (comp₌-assoc q (α ∙ p ⁻¹) (p′ ⁻¹)))

    changeEndpoints-reflect : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x ＝ x′) (q : y ＝ y′) {α β : x ＝ y}
      → changeEndpoints p q α =₁ changeEndpoints p q β → α =₁ β
    changeEndpoints-reflect p q c = cancel-right (p ⁻¹) (cancel-left q c)
```

A commuting square with sides `p` and `q` says exactly that the bottom edge
is the top edge with changed endpoints. The two conversions are recorded;
they are not claimed to be mutually inverse on higher data.

```agda
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    square-to-changeEndpoints : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x ＝ x′) (q : y ＝ y′) (α : x ＝ y) (β : x′ ＝ y′)
      → SquareCell₌ α β p q → changeEndpoints p q α =₁ β
    square-to-changeEndpoints p q α β square = comp-inv-right β p ∙
      (comp₌-cong square (id₌ (p ⁻¹)) ∙ (comp₌-assoc q α (p ⁻¹)) ⁻¹)

    changeEndpoints-to-square : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x ＝ x′) (q : y ＝ y′) (α : x ＝ y) (β : x′ ＝ y′)
      → changeEndpoints p q α =₁ β → SquareCell₌ α β p q
    changeEndpoints-to-square p q α β c = comp₌-cong c (id₌ p) ∙
      ((comp₌-assoc q (α ∙ p ⁻¹) p) ⁻¹ ∙ comp₌-cong (id₌ q) ((inv-comp-right α p) ⁻¹))
```

Postwhiskering commutes with endpoint change. A square whose top edge is
`α` gives a square whose top edge is `α` with changed endpoints, its sides
extended by the inverse endpoint changes.

```agda
  module _ {X B : CAT Γ} where
    open Terms.InContext B using (Term)
    open Terms.Equalities X using (_＝_)

    postWhisker-changeEndpoints : {C D : CAT Γ} (π : MAP C D) {x x′ y y′ : Term C}
      (p : x ＝ x′) (q : y ＝ y′) (α : x ＝ y)
      → (π ◁ changeEndpoints p q α) =₁ changeEndpoints (π ◁ p) (π ◁ q) (π ◁ α)
    postWhisker-changeEndpoints π p q α = comp₌-cong (id₌ (π ◁ q))
        (comp₌-cong (id₌ (π ◁ α)) (postWhisker-inverse π p) ∙ postWhisker-comp₌ π α (p ⁻¹)) ∙
      postWhisker-comp₌ π q (α ∙ p ⁻¹)

  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    changeEndpoints-extend-square : {D : CAT Γ} {u u′ v v′ x y : Term D}
      (p : u ＝ u′) (q : v ＝ v′) (α : u ＝ v)
      {l : u ＝ x} {r : v ＝ y} {δ : x ＝ y}
      → SquareCell₌ α δ l r
      → SquareCell₌ (changeEndpoints p q α) δ (l ∙ p ⁻¹) (r ∙ q ⁻¹)
    changeEndpoints-extend-square p q α {l} {r} {δ} square = comp₌-assoc δ l (p ⁻¹) ∙
      (comp₌-cong square (id₌ (p ⁻¹)) ∙
      ((comp₌-assoc r α (p ⁻¹)) ⁻¹ ∙
      (comp₌-cong (id₌ r) (inv-comp-left q (α ∙ p ⁻¹)) ∙
        comp₌-assoc r (q ⁻¹) (q ∙ (α ∙ p ⁻¹)))))
```

## Part 2: the endpoint-change functor

For fixed individual identifications `p` and `q`, endpoint change is a
functor between identification animae, composed of precomposition with
`p ⁻¹` and postcomposition with `q`; it is an equivalence. Evaluated at a
family it is endpoint change along the constant families; at `One`,
`const-One` identifies those with `p` and `q`.

```agda
module _ {Γ : Context} where
  module _ {C : CAT Γ} where
    open Terms.InContext C using (Term)

    changeEndpoints₌ : {D : CAT Γ} {x x′ y y′ : Term D}
      → x =₁ x′ → y =₁ y′ → MAP (Equal x y) (Equal x′ y′)
    changeEndpoints₌ p q = postcomp₌ q ∘ precomp₌ (p ⁻¹)

    changeEndpoints₌-isEquiv : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x =₁ x′) (q : y =₁ y′) → IsEquiv (changeEndpoints₌ p q)
    changeEndpoints₌-isEquiv p q = equiv-compose
      (precomp₌ (p ⁻¹)) (postcomp₌ q) (precomp₌-isEquiv (p ⁻¹)) (postcomp₌-isEquiv q)

  module _ {A C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities A using (_＝_)

    changeEndpoints₌-evaluate : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x =₁ x′) (q : y =₁ y′) (u : x ＝ y)
      → (changeEndpoints₌ p q ∘ u) =₁ changeEndpoints (const p) (const q) u
    changeEndpoints₌-evaluate p q u =
      comp₌-cong (id₌ (const q))
        (comp₌-cong (id₌ u) (const-inv p) ∙ precomp₌-evaluate (p ⁻¹) u) ∙
      (postcomp₌-evaluate q (precomp₌ (p ⁻¹) ∘ u) ∙
        comp-assoc u (precomp₌ (p ⁻¹)) (postcomp₌ q))

  module _ {C : CAT Γ} where
    open Terms.InContext C using (Term)

    changeEndpoints-const-One : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x =₁ x′) (q : y =₁ y′) (α : x =₁ y)
      → changeEndpoints (const p) (const q) α =₂ changeEndpoints p q α
    changeEndpoints-const-One p q α =
      comp₌-cong (const-One q) (comp₌-cong (id₌ α) (inv₌ ◁ const-One p))

  module _ {A C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities A using (_＝_)

    changeEndpoints₌-square : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x =₁ x′) (q : y =₁ y′) (u : x ＝ y)
      → SquareCell₌ u (changeEndpoints₌ p q ∘ u) (const p) (const q)
    changeEndpoints₌-square p q u = changeEndpoints-to-square (const p) (const q) u
      (changeEndpoints₌ p q ∘ u) ((changeEndpoints₌-evaluate p q u) ⁻¹)

    square-to-changeEndpoints₌ : {D : CAT Γ} {x x′ y y′ : Term D}
      (p : x =₁ x′) (q : y =₁ y′) (u : x ＝ y) (v : x′ ＝ y′)
      → SquareCell₌ u v (const p) (const q) → (changeEndpoints₌ p q ∘ u) =₁ v
    square-to-changeEndpoints₌ p q u v square =
      square-to-changeEndpoints (const p) (const q) u v square ∙ changeEndpoints₌-evaluate p q u

  module _ {A C : CAT Γ} where
    open Terms.InContext C using (Term)

    preWhisker-changeEndpoints-square : {D : CAT Γ} {x x′ y y′ : Term D}
      (i : MAP A C) (p : x =₁ x′) (q : y =₁ y′)
      → SquareCell₌ (preWhisker {f = x} {g = y} i) (preWhisker i ∘ changeEndpoints₌ p q)
          (const (p ▷ i)) (const (q ▷ i))
    preWhisker-changeEndpoints-square {x = x} {y = y} i p q =
      replace-edges₌ (comp-unitʳ (preWhisker i))
        (preWhisker i ◁ comp-unitʳ (changeEndpoints₌ p q))
        (replace-sides₌ (pre-constant p i) (pre-constant q i)
          (pre-square₌ i (changeEndpoints₌-square p q (id (Equal x y)))))
```

## Part 3: transport of finite diagrams

Changing every vertex of a diagram changes each edge by the endpoint changes
at its two vertices. A commuting triangle or pentagon remains commuting: the
endpoint changes of consecutive edges cancel. Replacing the edges of a
diagram with fixed vertices along identifications also preserves
commutativity.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    change-triangle-vertices : {D : CAT Γ} {v₀ v₁ v₂ w₀ w₁ w₂ : Term D}
      → TriangleDiagram {X = X} v₀ v₁ v₂
      → (v₀ ＝ w₀) → (v₁ ＝ w₁) → (v₂ ＝ w₂)
      → TriangleDiagram {X = X} w₀ w₁ w₂
    change-triangle-vertices T p₀ p₁ p₂ = triangle-diagram
      (changeEndpoints p₀ p₂ direct) (changeEndpoints p₀ p₁ first)
      (changeEndpoints p₁ p₂ second)
      where open TriangleDiagram T

    transport-triangle : {D : CAT Γ} {v₀ v₁ v₂ w₀ w₁ w₂ : Term D}
      (T : TriangleDiagram {X = X} v₀ v₁ v₂)
      (p₀ : v₀ ＝ w₀) (p₁ : v₁ ＝ w₁) (p₂ : v₂ ＝ w₂)
      → TriangleCommutes T → TriangleCommutes (change-triangle-vertices T p₀ p₁ p₂)
    transport-triangle T p₀ p₁ p₂ c =
      (changeEndpoints-comp p₀ p₁ p₂ (TriangleDiagram.second T) (TriangleDiagram.first T)) ⁻¹ ∙
        changeEndpoints-cong p₀ p₂ c

    change-pentagon-vertices : {D : CAT Γ}
      {v₀ v₁ v₂ v₃ v₄ w₀ w₁ w₂ w₃ w₄ : Term D}
      → PentagonDiagram {X = X} v₀ v₁ v₂ v₃ v₄
      → (v₀ ＝ w₀) → (v₁ ＝ w₁) → (v₂ ＝ w₂)
      → (v₃ ＝ w₃) → (v₄ ＝ w₄)
      → PentagonDiagram {X = X} w₀ w₁ w₂ w₃ w₄
    change-pentagon-vertices P p₀ p₁ p₂ p₃ p₄ = pentagon-diagram
      (changeEndpoints p₀ p₁ source-first) (changeEndpoints p₁ p₂ source-second)
      (changeEndpoints p₀ p₃ target-first) (changeEndpoints p₃ p₄ target-second)
      (changeEndpoints p₄ p₂ target-third)
      where open PentagonDiagram P

    transport-pentagon : {D : CAT Γ}
      {v₀ v₁ v₂ v₃ v₄ w₀ w₁ w₂ w₃ w₄ : Term D}
      (P : PentagonDiagram {X = X} v₀ v₁ v₂ v₃ v₄)
      (p₀ : v₀ ＝ w₀) (p₁ : v₁ ＝ w₁) (p₂ : v₂ ＝ w₂)
      (p₃ : v₃ ＝ w₃) (p₄ : v₄ ＝ w₄)
      → PentagonCommutes P → PentagonCommutes (change-pentagon-vertices P p₀ p₁ p₂ p₃ p₄)
    transport-pentagon P p₀ p₁ p₂ p₃ p₄ c =
      let open PentagonDiagram P
      in (changeEndpoints-comp₃ p₀ p₃ p₄ p₂ target-third target-second target-first) ⁻¹ ∙
        (changeEndpoints-cong p₀ p₂ c ∙
          changeEndpoints-comp p₀ p₁ p₂ source-second source-first)

  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)

    replace-triangle-edges : {D : CAT Γ} {v₀ v₁ v₂ : Term D}
      (T T′ : TriangleDiagram {X = X} v₀ v₁ v₂)
      → TriangleDiagram.direct T =₁ TriangleDiagram.direct T′
      → TriangleDiagram.first T =₁ TriangleDiagram.first T′
      → TriangleDiagram.second T =₁ TriangleDiagram.second T′
      → TriangleCommutes T′ → TriangleCommutes T
    replace-triangle-edges T T′ direct first second c =
      (comp₌-cong second first) ⁻¹ ∙ (c ∙ direct)

    replace-pentagon-edges : {D : CAT Γ} {v₀ v₁ v₂ v₃ v₄ : Term D}
      (P P′ : PentagonDiagram {X = X} v₀ v₁ v₂ v₃ v₄)
      → PentagonDiagram.source-first P =₁ PentagonDiagram.source-first P′
      → PentagonDiagram.source-second P =₁ PentagonDiagram.source-second P′
      → PentagonDiagram.target-first P =₁ PentagonDiagram.target-first P′
      → PentagonDiagram.target-second P =₁ PentagonDiagram.target-second P′
      → PentagonDiagram.target-third P =₁ PentagonDiagram.target-third P′
      → PentagonCommutes P′ → PentagonCommutes P
    replace-pentagon-edges P P′ s₁ s₂ t₁ t₂ t₃ c =
      (comp₌-cong (comp₌-cong t₃ t₂) t₁) ⁻¹ ∙ (c ∙ comp₌-cong s₂ s₁)
```

## Part 4: transport of squares and cancellation of encodings

Changing all four vertices of a commuting square, along endpoint changes
whose squares with the sides commute, gives a commuting square of the
changed horizontal edges. Conversely, from the transported square and the
two side squares one recovers the original square by reflecting through
endpoint change. (Filling a cube from five faces is `fill-cube₌` in
IdentificationSquares.)

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    transport-square : {D : CAT Γ} {a₀ a₁ b₀ b₁ x₀ x₁ y₀ y₁ : Term D}
      (L₀ : a₀ ＝ x₀) (L₁ : a₁ ＝ x₁)
      (R₀ : b₀ ＝ y₀) (R₁ : b₁ ＝ y₁)
      (q₀ : a₀ ＝ b₀) (q₁ : a₁ ＝ b₁)
      (u : a₀ ＝ a₁) (v : b₀ ＝ b₁)
      (α : x₀ ＝ x₁) (β : y₀ ＝ y₁)
      → SquareCell₌ u α L₀ L₁ → SquareCell₌ v β R₀ R₁ → SquareCell₌ u v q₀ q₁
      → SquareCell₌ α β (changeEndpoints L₀ R₀ q₀) (changeEndpoints L₁ R₁ q₁)
    transport-square L₀ L₁ R₀ R₁ q₀ q₁ u v α β left right middle =
      paste-square₌ {t = α} {m = v} {b = β}
        (paste-square₌ {t = α} {m = u} {b = v} (inverse-square₌ left) middle) right

    reflect-transported-square : {D : CAT Γ} {x x′ y y′ z z′ w w′ : Term D}
      (fs : x ＝ x′) (gs : y ＝ y′) (ft : z ＝ z′) (gt : w ＝ w′)
      (τs : x ＝ y) (τt : z ＝ w) (α : x ＝ z) (β : y ＝ w)
      (α′ : x′ ＝ z′) (β′ : y′ ＝ w′)
      → SquareCell₌ α α′ fs ft → SquareCell₌ β β′ gs gt
      → SquareCell₌ α′ β′ (changeEndpoints fs gs τs) (changeEndpoints ft gt τt)
      → SquareCell₌ α β τs τt
    reflect-transported-square fs gs ft gt τs τt α β α′ β′ left right transported =
      changeEndpoints-reflect fs gt
        (changeEndpoints-comp fs gs gt β τs ∙
        (comp₌-cong ((square-to-changeEndpoints gs gt β β′ right) ⁻¹)
          (id₌ (changeEndpoints fs gs τs)) ∙
        (transported ∙
        (comp₌-cong (id₌ (changeEndpoints ft gt τt))
          (square-to-changeEndpoints fs ft α α′ left) ∙
          (changeEndpoints-comp fs ft gt τt α) ⁻¹))))
```

Encoding an identification by endpoint changes and decoding it again
returns it; several bracketings are used by cone calculations, each with its
displayed associator route.

```agda
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    cancel-endpoint-changes : {D : CAT Γ} {a b x y : Term D}
      (L : a ＝ x) (R : b ＝ y) (γ : x ＝ y)
      → (R ∙ ((R ⁻¹ ∙ (γ ∙ L)) ∙ L ⁻¹)) =₁ γ
    cancel-endpoint-changes L R γ = comp-inv-right γ L ∙
      (comp₌-cong (comp-inv-left R (γ ∙ L)) (id₌ (L ⁻¹)) ∙
        (comp₌-assoc R (R ⁻¹ ∙ (γ ∙ L)) (L ⁻¹)) ⁻¹)

    restore-boundaries : {D : CAT Γ} {x x′ y y′ : Term D}
      (left : x′ ＝ x) (right : y′ ＝ y) (desired : x ＝ y)
      (image : x′ ＝ y′) → image =₁ (right ⁻¹ ∙ (desired ∙ left))
      → changeEndpoints left right image =₁ desired
    restore-boundaries left right desired image β = comp-inv-right desired left ∙
      (comp₌-cong (comp-inv-left right (desired ∙ left)) (id₌ (left ⁻¹)) ∙
        ((comp₌-assoc right (right ⁻¹ ∙ (desired ∙ left)) (left ⁻¹)) ⁻¹ ∙
          comp₌-cong (id₌ right) (comp₌-cong β (id₌ (left ⁻¹)))))

    inverse-route-square : {D : CAT Γ} {x x′ y z y′ : Term D}
      (p : x ＝ x′) (q : z ＝ y′) (r : y ＝ z)
      (α : x ＝ y) (β : x′ ＝ y′)
      → α =₁ (r ⁻¹ ∙ (q ⁻¹ ∙ (β ∙ p)))
      → SquareCell₌ α β p (q ∙ r)
    inverse-route-square p q r α β computation =
      cancel-two-inverses q r (β ∙ p) ∙ comp₌-cong (id₌ (q ∙ r)) computation

    inverse-route-transport : {D : CAT Γ} {x x′ y z y′ : Term D}
      (p : x ＝ x′) (q : z ＝ y′) (r : y ＝ z)
      (α : x ＝ y) (β : x′ ＝ y′)
      → α =₁ (r ⁻¹ ∙ (q ⁻¹ ∙ (β ∙ p)))
      → changeEndpoints p (q ∙ r) α =₁ β
    inverse-route-transport p q r α β computation =
      square-to-changeEndpoints p (q ∙ r) α β (inverse-route-square p q r α β computation)

    normalize-transported-square : {D : CAT Γ} {x x′ y y′ u v : Term D}
      (A : x ＝ x′) (B : y ＝ y′) (q : x ＝ y) (q′ : u ＝ v)
      (L : u ＝ x′) (R : v ＝ y′)
      → (q ∙ (A ⁻¹ ∙ L)) =₁ ((B ⁻¹ ∙ R) ∙ q′)
      → (changeEndpoints A B q ∙ L) =₁ (R ∙ q′)
    normalize-transported-square A B q q′ L R square = comp-inv-left B (R ∙ q′) ∙
      (comp₌-cong (id₌ B) (comp₌-assoc (B ⁻¹) R q′) ∙
      (comp₌-cong (id₌ B) square ∙
      (comp₌-cong (id₌ B) (comp₌-assoc q (A ⁻¹) L) ∙
        comp₌-assoc B (q ∙ A ⁻¹) L)))

    encoded-restriction-square : {D : CAT Γ} {a a′ b b′ x y : Term D}
      (A : a ＝ a′) (B : b ＝ b′)
      (u : a′ ＝ x) (v : b′ ＝ y) (δ : x ＝ y) (r : a ＝ b)
      → r =₁ ((v ∙ B) ⁻¹ ∙ (δ ∙ (u ∙ A)))
      → (δ ∙ u) =₁ (v ∙ changeEndpoints A B r)
    encoded-restriction-square A B u v δ r image =
      let square : (δ ∙ (u ∙ A)) =₁ ((v ∙ B) ∙ r)
          square = comp₌-cong (id₌ (v ∙ B)) (image ⁻¹) ∙
            (comp-inv-left (v ∙ B) (δ ∙ (u ∙ A))) ⁻¹
      in comp₌-assoc v B (r ∙ A ⁻¹) ∙
        (comp₌-assoc (v ∙ B) r (A ⁻¹) ∙
        (comp₌-cong square (id₌ (A ⁻¹)) ∙
        (comp₌-cong (comp₌-assoc δ u A) (id₌ (A ⁻¹)) ∙
          (comp-inv-right (δ ∙ u) A) ⁻¹)))
```

## Part 5: restricting specified identifications

An identification `α : F = G`, restricted along `q` and then `r`, agrees
with its restriction along a functor `q′` identified with `q ∘ r` by `δ`,
up to the specified changes of source and target. With supplied
identifications of the restricted endpoints, the same holds for the
endpoint-changed identifications.

```agda
module _ {Γ : Context} where
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    identification-restriction : {R T X Y : CAT Γ} {F G : MAP X Y}
      (α : F ＝ G) (q : MAP T X) (r : MAP R T) (q′ : MAP R X)
      (δ : (q ∘ r) ＝ q′)
      → SquareCell₌ ((α ▷ q) ▷ r) (α ▷ q′)
          ((F ◁ δ) ∙ const (comp-assoc r q F)) ((G ◁ δ) ∙ const (comp-assoc r q G))
    identification-restriction {F = F} {G} α q r q′ δ =
      ((comp₌-assoc (G ◁ δ) (const (comp-assoc r q G)) ((α ▷ q) ▷ r)) ⁻¹ ∙
        (comp₌-cong (id₌ (G ◁ δ)) ((preWhisker-comp α q r) ⁻¹) ∙
          (comp₌-assoc (G ◁ δ) (α ▷ (q ∘ r)) (const (comp-assoc r q F)) ∙
            (comp₌-cong (interchange α δ) (id₌ (const (comp-assoc r q F))) ∙
              (comp₌-assoc (α ▷ q′) (F ◁ δ) (const (comp-assoc r q F))) ⁻¹)))) ⁻¹

    module EndpointRestriction {R T X Y : CAT Γ}
      {F G : MAP X Y} (α : F ＝ G)
      (q : MAP T X) (r : MAP R T) (q′ : MAP R X) (δ : (q ∘ r) ＝ q′)
      {L O : MAP T Y} {L′ O′ : MAP R Y}
      (l : (F ∘ q) ＝ L) (l′ : (F ∘ q′) ＝ L′)
      (o : (G ∘ q) ＝ O) (o′ : (G ∘ q′) ＝ O′)
      (u : (L ∘ r) ＝ L′) (v : (O ∘ r) ＝ O′) where

      source-change = (F ◁ δ) ∙ const (comp-assoc r q F)
      target-change = (G ◁ δ) ∙ const (comp-assoc r q G)
      before = changeEndpoints l o (α ▷ q)
      after = changeEndpoints l′ o′ (α ▷ q′)

      square : SquareCell₌ source-change u (l ▷ r) l′
        → SquareCell₌ target-change v (o ▷ r) o′
        → SquareCell₌ u v (before ▷ r) after
      square leftSquare outputSquare =
        let restricted = (α ▷ q) ▷ r
            normalize : (before ▷ r) =₁ changeEndpoints (l ▷ r) (o ▷ r) restricted
            normalize = comp₌-cong (id₌ (o ▷ r))
                (comp₌-cong (id₌ restricted) (preWhisker-inverse l r) ∙
                  preWhisker-comp₌ (α ▷ q) (l ⁻¹) r) ∙
              preWhisker-comp₌ o ((α ▷ q) ∙ l ⁻¹) r
            transported = transport-square (l ▷ r) l′ (o ▷ r) o′ restricted (α ▷ q′)
              source-change target-change u v leftSquare outputSquare
              (transpose-square₌ (identification-restriction α q r q′ δ))
        in replace-sides₌ (normalize ⁻¹) (id₌ after) transported
```
