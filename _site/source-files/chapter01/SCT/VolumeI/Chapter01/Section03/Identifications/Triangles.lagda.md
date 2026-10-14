# Specified triangles under restriction and postcomposition

A *triangle* is an identification `b : π ∘ h =₁ x`: the functor `x` factors
through `π` with factor `h` (Section03.Factorizations views it so). Many
constructions specify such triangles and must compute how they change when
the factor is restricted along a functor `r`, or when `π` is postcomposed with
a functor `F`. This module provides the two operations,

    restrict-triangle π h b r : π ∘ (h ∘ r) =₁ x ∘ r
    post-triangle F π h b     : (F ∘ π) ∘ h =₁ F ∘ x,

and their effect on *squares of triangles*. Given triangles `b` for `h` and
`b′` for `h′`, an identification family `δ : h = h′` *lies over*
`α : x = x′` when the identification square

    SquareCell₌ (π ◁ δ) α b b′,   that is   b′ ∙ (π ◁ δ) =₁ α ∙ b,

commutes. For families, the fixed triangles enter as constant families;
`unconst-sides₌` converts the instance at `One` into the individual equation.
Restriction and postcomposition carry squares to squares. Postcomposing
twice agrees with postcomposing with the composite, and restricting twice
agrees with restricting along the composite, both up to the external
associators: these two laws use the whiskered pentagon. The final part
records the unit computations, which use Kelly's lemmas.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.Triangles where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌;
    module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
```

## Restriction and postcomposition

A triangle whose value is itself a composite `f ∘ ρ` is the cell of a square
of functors; postcomposing it with `F` and reassociating the value gives
`post-square-cell`.

```agda
module _ {Γ : Context} where
  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    restrict-triangle : {K C : CAT Γ} (π : MAP K C) (z : Term K) {x : Term C}
      → (π ∘ z) =₁ x → (r : MAP R X) → (π ∘ (z ∘ r)) =₁ (x ∘ r)
    restrict-triangle π z b r = (b ▷ r) ∙ (comp-assoc r z π) ⁻¹

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-triangle : {K A B : CAT Γ} (F : MAP A B) (π : MAP K A) (z : Term K)
      {x : Term A} → (π ∘ z) =₁ x → ((F ∘ π) ∘ z) =₁ (F ∘ x)
    post-triangle F π z b = (F ◁ b) ∙ comp-assoc z π F

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-square-cell : {K C D : CAT Γ} (F : MAP C D)
      (ρ : MAP R X) (x : Term C) (π : MAP K C) (h : MAP R K)
      → (π ∘ h) =₁ (x ∘ ρ) → ((F ∘ π) ∘ h) =₁ ((F ∘ x) ∘ ρ)
    post-square-cell F ρ x π h b = (comp-assoc ρ x F) ⁻¹ ∙ post-triangle F π h b
```

## Squares of triangles

Restricting a square of triangles along `r` gives a square of the restricted
triangles: whisker the square by `r`, then move the restriction inside the
postwhiskering by the mixed whiskering law. Changing the functor along which
a fixed triangle is restricted gives the corresponding square by
interchange. Both are stated for families; the instances at `One` are
recorded with the individual triangles as sides.

```agda
module _ {Γ : Context} where
  private
    module _ {A R X : CAT Γ} where
      open Terms.InContext X using (Term)

      restricted-side : {K C : CAT Γ} (π : MAP K C) (z : Term K) {x : Term C}
        (b : (π ∘ z) =₁ x) (r : MAP R X)
        → ((const {P = A} b ▷ r) ∙ (const (comp-assoc r z π)) ⁻¹) =₁
            const (restrict-triangle π z b r)
      restricted-side  π z b r =
        const-comp {X = A} (b ▷ r) ((comp-assoc r z π) ⁻¹) ∙
          comp₌-cong (pre-constant b r) ((const-inv (comp-assoc r z π)) ⁻¹)

  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    restrict-square : {K C : CAT Γ} (π : MAP K C)
      {z z′ : Term K} {x x′ : Term C}
      (δ : z ＝ z′) (α : x ＝ x′)
      (b : (π ∘ z) =₁ x) (b′ : (π ∘ z′) =₁ x′) (r : MAP R X)
      → SquareCell₌ (π ◁ δ) α (const b) (const b′)
      → SquareCell₌ (π ◁ (δ ▷ r)) (α ▷ r)
          (const (restrict-triangle π z b r)) (const (restrict-triangle π z′ b′ r))
    restrict-square π {z} {z′} δ α b b′ r square =
      replace-sides₌ (restricted-side π z b r) (restricted-side π z′ b′ r)
        (paste-square₌ {t = π ◁ (δ ▷ r)} {m = (π ◁ δ) ▷ r} {b = α ▷ r}
          (inverse-square₌ {t = (π ◁ δ) ▷ r} {b = π ◁ (δ ▷ r)}
            {l = const (comp-assoc r z π)} {r = const (comp-assoc r z′ π)}
            (whisker-mixed δ r π))
          (pre-square₌ r square))

    restrict-change-square : {K C : CAT Γ} (π : MAP K C)
      (z : Term K) (x : Term C) (b : (π ∘ z) =₁ x)
      {r s : MAP R X} (γ : r ＝ s)
      → SquareCell₌ (π ◁ (z ◁ γ)) (x ◁ γ)
          (const (restrict-triangle π z b r)) (const (restrict-triangle π z b s))
    restrict-change-square π z x b {r} {s} γ =
      replace-sides₌ (restricted-side π z b r) (restricted-side π z b s)
        (paste-square₌ {t = π ◁ (z ◁ γ)} {m = (π ∘ z) ◁ γ} {b = x ◁ γ}
          (inverse-square₌ {t = (π ∘ z) ◁ γ} {b = π ◁ (z ◁ γ)}
            {l = const (comp-assoc r z π)} {r = const (comp-assoc s z π)}
            (postWhisker-comp γ z π))
          (replace-sides₌ ((pre-constant b r) ⁻¹) ((pre-constant b s) ⁻¹)
            (interchange-fixedOuter b γ)))

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    restrict-square-One : {K C : CAT Γ} (π : MAP K C)
      {z z′ : Term K} {x x′ : Term C}
      (δ : z =₁ z′) (α : x =₁ x′)
      (b : (π ∘ z) =₁ x) (b′ : (π ∘ z′) =₁ x′) (r : MAP R X)
      → SquareCell₌ (π ◁ δ) α b b′
      → SquareCell₌ (π ◁ (δ ▷ r)) (α ▷ r)
          (restrict-triangle π z b r) (restrict-triangle π z′ b′ r)
    restrict-square-One π δ α b b′ r square =
      unconst-sides₌ (restrict-square π δ α b b′ r (const-sides₌ square))

    restrict-change-square-One : {K C : CAT Γ} (π : MAP K C)
      (z : Term K) (x : Term C) (b : (π ∘ z) =₁ x)
      {r s : MAP R X} (γ : r =₁ s)
      → SquareCell₌ (π ◁ (z ◁ γ)) (x ◁ γ)
          (restrict-triangle π z b r) (restrict-triangle π z b s)
    restrict-change-square-One π z x b γ =
      unconst-sides₌ (restrict-change-square π z x b γ)
```

A square of triangles can also be stated before restricting the triangles:
moving the associator from the restricted triangle to the edge gives an
equivalent square, recorded in the forward direction used by its clients.

```agda
  module _ {R T X : CAT Γ} where
    open Terms.InContext X using (Term)

    unrestrict-square : {A : CAT Γ} (π : Term A)
      (q : MAP T X) (r : MAP R T) (q′ : MAP R X)
      {p : MAP T A} {p′ : MAP R A}
      (δ : (q ∘ r) =₁ q′) (b : (π ∘ q) =₁ p)
      (b′ : (π ∘ q′) =₁ p′) (c : (p ∘ r) =₁ p′)
      → (b′ ∙ (π ◁ δ)) =₂ (c ∙ restrict-triangle π q b r)
      → (b′ ∙ ((π ◁ δ) ∙ comp-assoc r q π)) =₂ (c ∙ (b ▷ r))
    unrestrict-square π q r q′ δ b b′ c square =
      let A = comp-assoc r q π
      in comp₌-cong (id₌ c) (inv-comp-right (b ▷ r) A) ∙
        (comp₌-assoc c ((b ▷ r) ∙ A ⁻¹) A ∙
          (comp₌-cong square (id₌ A) ∙ (comp₌-assoc b′ (π ◁ δ) A) ⁻¹))
```

Two triangles and a square identify two projected composites. Cancelling the
common triangle `c` reflects the comparison of projected routes.

```agda
  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    projected-square : {K C : CAT Γ} {z₀ h₁ z₂ h₃ : Term K} {z₁ z₃ : Term C}
      (π : MAP K C) (ρ : h₁ ＝ h₃) (τ : z₀ ＝ h₁)
      (υ : z₂ ＝ h₃) (δ : z₀ ＝ z₂)
      (b : (π ∘ h₁) =₁ z₁) (c : (π ∘ h₃) =₁ z₃)
      (α : z₁ ＝ z₃)
      (q : ((π ∘ z₀) ＝ z₁)) (q′ : ((π ∘ z₂) ＝ z₃))
      → SquareCell₌ (π ◁ ρ) α (const b) (const c)
      → (const b ∙ (π ◁ τ)) =₁ q
      → (const c ∙ (π ◁ υ)) =₁ q′
      → (q′ ∙ (π ◁ δ)) =₁ (α ∙ q)
      → (π ◁ (ρ ∙ τ)) =₁ (π ◁ (υ ∙ δ))
    projected-square π ρ τ υ δ b c α q q′ top left bottom square =
      let left-normal = comp₌-cong (id₌ α) left ∙
            (comp₌-assoc α (const b) (π ◁ τ) ∙
              (comp₌-cong top (id₌ (π ◁ τ)) ∙ project-composite π ρ τ (const c)))
          right-normal = square ∙
            (comp₌-cong bottom (id₌ (π ◁ δ)) ∙ project-composite π υ δ (const c))
      in cancel-left (const c) (right-normal ⁻¹ ∙ left-normal)
```

## Naturality of postcomposition

Postcomposing a triangle is natural in the postcomposed functor and,
given a square of triangles, in the factor. The same holds for
postcomposition of square cells. All four are stated for families.

```agda
module _ {Γ : Context} where
  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    post-triangle-outer : {K C D : CAT Γ} {F G : MAP C D}
      (θ : F ＝ G) (π : MAP K C) (t : Term K) {p : Term C}
      (b : (π ∘ t) =₁ p)
      → SquareCell₌ ((θ ▷ π) ▷ t) (θ ▷ p)
          (const (post-triangle F π t b)) (const (post-triangle G π t b))
    post-triangle-outer  {F = F} {G} θ π t {p} b =
      replace-sides₌ (const-comp {X = A} (F ◁ b) (comp-assoc t π F))
        (const-comp {X = A} (G ◁ b) (comp-assoc t π G))
        (paste-square₌ {t = (θ ▷ π) ▷ t} {m = θ ▷ (π ∘ t)} {b = θ ▷ p}
          (preWhisker-comp θ π t) ((interchange-fixedInner θ b) ⁻¹))

    post-triangle-inner : {K C D : CAT Γ} (F : MAP C D) (π : MAP K C)
      {t t′ : Term K} {p p′ : Term C}
      (δ : t ＝ t′) (α : p ＝ p′)
      (b : (π ∘ t) =₁ p) (b′ : (π ∘ t′) =₁ p′)
      → SquareCell₌ (π ◁ δ) α (const b) (const b′)
      → SquareCell₌ ((F ∘ π) ◁ δ) (F ◁ α)
          (const (post-triangle F π t b)) (const (post-triangle F π t′ b′))
    post-triangle-inner  F π {t} {t′} δ α b b′ square =
      replace-sides₌
        (const-comp {X = A} (F ◁ b) (comp-assoc t π F) ∙
          comp₌-cong (post-constant F b) (id₌ (const (comp-assoc t π F))))
        (const-comp {X = A} (F ◁ b′) (comp-assoc t′ π F) ∙
          comp₌-cong (post-constant F b′) (id₌ (const (comp-assoc t′ π F))))
        (paste-square₌ {t = (F ∘ π) ◁ δ} {m = F ◁ (π ◁ δ)} {b = F ◁ α}
          (postWhisker-comp δ π F) (post-square₌ F square))

  module _ {A R X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    post-square-cell-outer : {K C D : CAT Γ}
      (ρ : MAP R X) (x : Term C) (π : MAP K C) (h : MAP R K)
      (b : (π ∘ h) =₁ (x ∘ ρ)) {F F′ : MAP C D} (θ : F ＝ F′)
      → SquareCell₌ ((θ ▷ π) ▷ h) ((θ ▷ x) ▷ ρ)
          (const (post-square-cell F ρ x π h b)) (const (post-square-cell F′ ρ x π h b))
    post-square-cell-outer  ρ x π h b {F} {F′} θ =
      replace-sides₌
        (const-comp {X = A} ((comp-assoc ρ x F) ⁻¹) (post-triangle F π h b) ∙
          comp₌-cong ((const-inv (comp-assoc ρ x F)) ⁻¹) (id₌ (const (post-triangle F π h b))))
        (const-comp {X = A} ((comp-assoc ρ x F′) ⁻¹) (post-triangle F′ π h b) ∙
          comp₌-cong ((const-inv (comp-assoc ρ x F′)) ⁻¹) (id₌ (const (post-triangle F′ π h b))))
        (paste-square₌ {t = (θ ▷ π) ▷ h} {m = θ ▷ (x ∘ ρ)} {b = (θ ▷ x) ▷ ρ}
          (post-triangle-outer θ π h b)
          (inverse-square₌ {t = (θ ▷ x) ▷ ρ} {b = θ ▷ (x ∘ ρ)}
            {l = const (comp-assoc ρ x F)} {r = const (comp-assoc ρ x F′)}
            (preWhisker-comp θ x ρ)))

    post-square-cell-inner : {K C D : CAT Γ}
      (ρ : MAP R X) (π : MAP K C) (F : MAP C D)
      {x x′ : Term C} {h h′ : MAP R K}
      (b : (π ∘ h) =₁ (x ∘ ρ)) (b′ : (π ∘ h′) =₁ (x′ ∘ ρ))
      (α : x ＝ x′) (δ : h ＝ h′)
      → SquareCell₌ (π ◁ δ) (α ▷ ρ) (const b) (const b′)
      → SquareCell₌ ((F ∘ π) ◁ δ) ((F ◁ α) ▷ ρ)
          (const (post-square-cell F ρ x π h b)) (const (post-square-cell F ρ x′ π h′ b′))
    post-square-cell-inner  ρ π F {x} {x′} {h} {h′} b b′ α δ square =
      replace-sides₌
        (const-comp {X = A} ((comp-assoc ρ x F) ⁻¹) (post-triangle F π h b) ∙
          comp₌-cong ((const-inv (comp-assoc ρ x F)) ⁻¹) (id₌ (const (post-triangle F π h b))))
        (const-comp {X = A} ((comp-assoc ρ x′ F) ⁻¹) (post-triangle F π h′ b′) ∙
          comp₌-cong ((const-inv (comp-assoc ρ x′ F)) ⁻¹) (id₌ (const (post-triangle F π h′ b′))))
        (paste-square₌ {t = (F ∘ π) ◁ δ} {m = F ◁ (α ▷ ρ)} {b = (F ◁ α) ▷ ρ}
          (post-triangle-inner F π δ (α ▷ ρ) b b′ square)
          (inverse-square₌ {t = (F ◁ α) ▷ ρ} {b = F ◁ (α ▷ ρ)}
            {l = const (comp-assoc ρ x F)} {r = const (comp-assoc ρ x′ F)}
            (whisker-mixed α ρ F)))
```

## Successive restriction and postcomposition

Restricting along `σ` and then `τ` agrees with restricting along `σ ∘ τ`:
the factor associator lies over the value associator. Postcomposing a square
cell with `g` and then `f` agrees with postcomposing with `f ∘ g`, up to the
associators at the source and target. Both proofs solve a whiskered
pentagon for a corner.

```agda
module _ {Γ : Context} where
  module _ {Q R X : CAT Γ} where
    open Terms.InContext X using (Term)

    restrict-triangle-assoc : {K C : CAT Γ} (π : MAP K C) (z : Term K)
      {x : Term C} (b : (π ∘ z) =₁ x) (σ : MAP R X) (τ : MAP Q R)
      → SquareCell₌ (π ◁ comp-assoc τ σ z) (comp-assoc τ σ x)
          (restrict-triangle π (z ∘ σ) (restrict-triangle π z b σ) τ)
          (restrict-triangle π z b (σ ∘ τ))
    restrict-triangle-assoc π z {x} b σ τ =
      let A = comp-assoc τ σ x
          B = (b ▷ σ) ▷ τ
          E = comp-assoc σ z π ▷ τ
          D′ = comp-assoc τ (z ∘ σ) π
          B′ = comp-assoc τ σ (π ∘ z)
          A′ = comp-assoc (σ ∘ τ) z π
          C′ = π ◁ comp-assoc τ σ z
          b′ = b ▷ (σ ∘ τ)
          tail = E ⁻¹ ∙ D′ ⁻¹
          expand = comp₌-cong
            ((comp₌-assoc A B (E ⁻¹)) ⁻¹ ∙
              comp₌-cong (id₌ A)
                (comp₌-cong (id₌ B) (preWhisker-inverse (comp-assoc σ z π) τ) ∙
                  preWhisker-comp₌ (b ▷ σ) ((comp-assoc σ z π) ⁻¹) τ))
            (id₌ (D′ ⁻¹))
          exchange = comp₌-cong
            (comp₌-cong (preWhisker-comp-One b σ τ) (id₌ (E ⁻¹)))
            (id₌ (D′ ⁻¹))
          regroup = comp₌-assoc b′ B′ tail ∙ comp₌-assoc (b′ ∙ B′) (E ⁻¹) (D′ ⁻¹)
          corner = solve-pentagon A′ B′ C′ D′ E (pentagon-whiskered τ σ z π)
          original : ((A ∙ (restrict-triangle π z b σ ▷ τ)) ∙ D′ ⁻¹) =₂
            (restrict-triangle π z b (σ ∘ τ) ∙ C′)
          original = (comp₌-assoc b′ (A′ ⁻¹) C′) ⁻¹ ∙
            (comp₌-cong (id₌ b′) corner ∙ (regroup ∙ (exchange ∙ expand)))
      in comp₌-assoc A (restrict-triangle π z b σ ▷ τ) (D′ ⁻¹) ∙ original ⁻¹

    restrict-triangle-twice : {K C : CAT Γ} (π : MAP K C) (z : Term K)
      {x : Term C} (b : (π ∘ z) =₁ x) (σ : MAP R X) (τ : MAP Q R)
      → ((comp-assoc τ σ x ∙ (restrict-triangle π z b σ ▷ τ)) ∙
            (comp-assoc τ (z ∘ σ) π) ⁻¹) =₂
          (restrict-triangle π z b (σ ∘ τ) ∙ (π ◁ comp-assoc τ σ z))
    restrict-triangle-twice π z {x} b σ τ = (restrict-triangle-assoc π z b σ τ) ⁻¹ ∙
      comp₌-assoc (comp-assoc τ σ x) (restrict-triangle π z b σ ▷ τ)
        ((comp-assoc τ (z ∘ σ) π) ⁻¹)

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-square-cell-comp : {K C D E : CAT Γ}
      (ρ : MAP R X) (s : Term C) (π : MAP K C) (h : MAP R K)
      (b : (π ∘ h) =₁ (s ∘ ρ)) (g : MAP C D) (f : MAP D E)
      → SquareCell₌ (comp-assoc π g f ▷ h) (comp-assoc s g f ▷ ρ)
          (post-square-cell (f ∘ g) ρ s π h b)
          (post-square-cell f ρ (g ∘ s) (g ∘ π) h (post-square-cell g ρ s π h b))
    post-square-cell-comp ρ s π h b g f =
      let inputLeft = comp-assoc h π (f ∘ g)
          middleLeft = (f ∘ g) ◁ b
          outputLeft = (comp-assoc ρ s (f ∘ g)) ⁻¹
          inputRight = (f ◁ comp-assoc h π g) ∙ comp-assoc h (g ∘ π) f
          middleRight = f ◁ (g ◁ b)
          outputRight = (comp-assoc ρ (g ∘ s) f) ⁻¹ ∙ (f ◁ (comp-assoc ρ s g) ⁻¹)
          atSource = comp-assoc π g f ▷ h
          afterInput = comp-assoc (π ∘ h) g f
          beforeOutput = comp-assoc (s ∘ ρ) g f
          atTarget = comp-assoc s g f ▷ ρ
          inputSquare : SquareCell₌ atSource afterInput inputLeft inputRight
          inputSquare = (pentagon-whiskered h π g f) ⁻¹
          middleSquare : SquareCell₌ afterInput beforeOutput middleLeft middleRight
          middleSquare = (postWhisker-comp-One b g f) ⁻¹
          outputSquare : SquareCell₌ beforeOutput atTarget outputLeft outputRight
          outputSquare = pentagon-left-corner beforeOutput (comp-assoc ρ s (f ∘ g))
              (f ◁ comp-assoc ρ s g) (comp-assoc ρ (g ∘ s) f) atTarget
              (pentagon-whiskered ρ s g f) ∙
            (comp₌-assoc ((comp-assoc ρ (g ∘ s) f) ⁻¹)
              ((f ◁ comp-assoc ρ s g) ⁻¹) beforeOutput ∙
            comp₌-cong
              (comp₌-cong (id₌ ((comp-assoc ρ (g ∘ s) f) ⁻¹))
                (postWhisker-inverse f (comp-assoc ρ s g)))
              (id₌ beforeOutput))
          assembled : SquareCell₌ atSource atTarget
            (outputLeft ∙ (middleLeft ∙ inputLeft)) (outputRight ∙ (middleRight ∙ inputRight))
          assembled = paste-square₌ (paste-square₌ inputSquare middleSquare) outputSquare
          outside = (comp-assoc ρ (g ∘ s) f) ⁻¹
          firstImage = f ◁ (comp-assoc ρ s g) ⁻¹
          lastImage = f ◁ comp-assoc h π g
          finalInput = comp-assoc h (g ∘ π) f
          mergeImages : (firstImage ∙ (middleRight ∙ lastImage)) =₂
            (f ◁ post-square-cell g ρ s π h b)
          mergeImages = (postWhisker-comp₌ f ((comp-assoc ρ s g) ⁻¹) ((g ◁ b) ∙ comp-assoc h π g)) ⁻¹ ∙
            comp₌-cong (id₌ firstImage) ((postWhisker-comp₌ f (g ◁ b) (comp-assoc h π g)) ⁻¹)
          normalizeRight : (outputRight ∙ (middleRight ∙ inputRight)) =₂
            post-square-cell f ρ (g ∘ s) (g ∘ π) h (post-square-cell g ρ s π h b)
          normalizeRight = comp₌-cong (id₌ outside)
            (comp₌-cong mergeImages (id₌ finalInput) ∙
            ((comp₌-assoc firstImage (middleRight ∙ lastImage) finalInput) ⁻¹ ∙
              comp₌-cong (id₌ firstImage) ((comp₌-assoc middleRight lastImage finalInput) ⁻¹))) ∙
            comp₌-assoc outside firstImage (middleRight ∙ (lastImage ∙ finalInput))
      in assembled ∙ (comp₌-cong normalizeRight (id₌ atSource)) ⁻¹
```

## Unit computations

Restricting a triangle along an identity functor agrees with the right
unitors, and postcomposing with an identity functor agrees with the left
unitors (Kelly's lemmas). The projected unit arguments below combine these
computations with three supplied triangles; they are used for the unit
laws of product functors and of first-factor substitution.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    restrict-triangle-id : {K C : CAT Γ} (π : MAP K C)
      (z : Term K) (x : Term C) (b : (π ∘ z) =₁ x)
      → (comp-unitʳ x ∙ restrict-triangle π z b (id X)) =₂ (b ∙ (π ◁ comp-unitʳ z))
    restrict-triangle-id  π z x b =
      let A = comp-assoc (id X) z π
          normalize = comp-inv-right (π ◁ comp-unitʳ z) A ∙
            comp₌-cong (right-unitor-comp z π) (id₌ (A ⁻¹))
      in comp₌-cong (id₌ b) normalize ∙
        (comp₌-assoc b (comp-unitʳ (π ∘ z)) (A ⁻¹) ∙
        (comp₌-cong (preWhisker-id-One b) (id₌ (A ⁻¹)) ∙
          (comp₌-assoc (comp-unitʳ x) (b ▷ id X) (A ⁻¹)) ⁻¹))

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-square-cell-id : {K C : CAT Γ}
      (ρ : MAP R X) (x : Term C) (π : MAP K C) (h : MAP R K)
      (b : (π ∘ h) =₁ (x ∘ ρ))
      → ((comp-unitˡ x ▷ ρ) ∙ post-square-cell (id C) ρ x π h b) =₂
          (b ∙ (comp-unitˡ π ▷ h))
    post-square-cell-id ρ x π h b =
      let A = comp-assoc ρ x (id _)
          B = comp-assoc h π (id _)
          first = comp-inv-right (comp-unitˡ (x ∘ ρ)) A ∙
            comp₌-cong ((left-unitor-comp ρ x) ⁻¹) (id₌ (A ⁻¹))
      in comp₌-cong (id₌ b) (left-unitor-comp h π) ∙
        (comp₌-assoc b (comp-unitˡ (π ∘ h)) B ∙
        (comp₌-cong (postWhisker-id-One b) (id₌ B) ∙
        ((comp₌-assoc (comp-unitˡ (x ∘ ρ)) (id _ ◁ b) B) ⁻¹ ∙
        (comp₌-cong first (id₌ ((id _ ◁ b) ∙ B)) ∙
          (comp₌-assoc (comp-unitˡ x ▷ ρ) (A ⁻¹) ((id _ ◁ b) ∙ B)) ⁻¹))))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-triangle-id : {Y A : CAT Γ} (π : MAP Y A) (t : Term Y)
      {q : Term A} (b : (π ∘ t) =₁ q)
      → (comp-unitˡ q ∙ post-triangle (id A) π t b) =₂ (b ∙ (comp-unitˡ π ▷ t))
    post-triangle-id π t b = comp₌-cong (id₌ b) (left-unitor-comp t π) ∙
      (comp₌-assoc b (comp-unitˡ (π ∘ t)) (comp-assoc t π (id _)) ∙
      (comp₌-cong (postWhisker-id-One b) (id₌ (comp-assoc t π (id _))) ∙
        (comp₌-assoc (comp-unitˡ _) (id _ ◁ b) (comp-assoc t π (id _))) ⁻¹))
```

The projected-triangle calculation pastes three supplied triangles after
projecting a composite. It is pure vertical calculus.

```agda
  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    projected-triangles : {C : CAT Γ} {a b c c′ d y z : Term C}
      (frame : c =₁ z) (out : b =₁ c) (step : a =₁ b)
      (unit : y =₁ z) (middle : b =₁ y)
      (coordinate : d =₁ y) (transport : a =₁ d)
      (result-frame : c′ =₁ z) (result : d =₁ c′)
      (projected : a =₁ z)
      → projected =₂ ((frame ∙ out) ∙ step)
      → (frame ∙ out) =₂ (unit ∙ middle)
      → (middle ∙ step) =₂ (coordinate ∙ transport)
      → (unit ∙ coordinate) =₂ (result-frame ∙ result)
      → projected =₂ (result-frame ∙ (result ∙ transport))
    projected-triangles frame out step unit middle coordinate transport result-frame result
      projected project out-triangle step-triangle coordinate-unit =
      comp₌-assoc result-frame result transport ∙
        (comp₌-cong coordinate-unit (id₌ transport) ∙
        ((comp₌-assoc unit coordinate transport) ⁻¹ ∙
        (comp₌-cong (id₌ unit) step-triangle ∙
        (comp₌-assoc unit middle step ∙
        (comp₌-cong out-triangle (id₌ step) ∙ project)))))
```

The left unit argument identifies the projection of a composite `out ∙ step`
with the projection of the restricted unit route, when `step` is a
postcomposition with an endofunctor `J` identified with the identity by
`δ`. The right unit argument is dual, with `J` acting on the source.

```agda
  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    left-unit-projection : {K C : CAT Γ}
      (ρ : MAP R X) (x : Term C) (π : MAP K C) (h h′ : MAP R K)
      (J : MAP K K) (δ : J =₁ (id K))
      (b : (π ∘ h) =₁ (x ∘ ρ))
      (b′ : (π ∘ h′) =₁ ((id C ∘ x) ∘ ρ))
      (bJ : (π ∘ J) =₁ (id C ∘ π))
      (out : h′ =₁ h) (step : (J ∘ h) =₁ h′)
      → (comp-unitʳ π ∙ (π ◁ δ)) =₂ (comp-unitˡ π ∙ bJ)
      → (b ∙ (π ◁ out)) =₂ ((comp-unitˡ x ▷ ρ) ∙ b′)
      → (b′ ∙ (π ◁ step)) =₂
          (post-square-cell (id C) ρ x π h b ∙ restrict-triangle π J bJ h)
      → (π ◁ (out ∙ step)) =₂ (π ◁ (comp-unitˡ h ∙ (δ ▷ h)))
    left-unit-projection ρ x π h h′ J δ b b′ bJ out step unit-triangle out-triangle step-triangle =
      let e = post-square-cell (id _) ρ x π h b
          left-normal = projected-triangles
            b (π ◁ out) (π ◁ step) (comp-unitˡ x ▷ ρ) b′
            e (restrict-triangle π J bJ h) b (comp-unitˡ π ▷ h) (b ∙ (π ◁ (out ∙ step)))
            (project-composite π out step b) out-triangle step-triangle
            (post-square-cell-id ρ x π h b)
          A = comp-assoc h (id _) π
          triangle-solved : (π ◁ comp-unitˡ h) =₂ ((comp-unitʳ π ▷ h) ∙ A ⁻¹)
          triangle-solved =
            (comp-inv-right (π ◁ comp-unitˡ h) A ∙
              comp₌-cong (triangle-whiskered h π) (id₌ (A ⁻¹))) ⁻¹
          pre-square = restrict-square-One π δ (comp-unitˡ π) bJ (comp-unitʳ π) h unit-triangle
          right-normal = comp₌-cong (id₌ b)
              (pre-square ∙ comp₌-cong triangle-solved (id₌ (π ◁ (δ ▷ h)))) ∙
            (comp₌-assoc b (π ◁ comp-unitˡ h) (π ◁ (δ ▷ h)) ∙
              project-composite π (comp-unitˡ h) (δ ▷ h) b)
      in cancel-left b (right-normal ⁻¹ ∙ left-normal)

  post-square-cell-right-unit : {R C D : CAT Γ}
    (ρ : MAP R C) (f : MAP C D) (J : MAP R R) (δ : J =₁ (id R))
    (bJ : (ρ ∘ J) =₁ (id C ∘ ρ))
    → (comp-unitʳ ρ ∙ (ρ ◁ δ)) =₂ (comp-unitˡ ρ ∙ bJ)
    → ((comp-unitʳ f ▷ ρ) ∙ post-square-cell f ρ (id C) ρ J bJ) =₂
        (comp-unitʳ (f ∘ ρ) ∙ ((f ∘ ρ) ◁ δ))
  post-square-cell-right-unit ρ f J δ bJ unit-triangle =
    let A = comp-assoc ρ (id _) f
        B = comp-assoc J ρ f
        C′ = comp-assoc (id _) ρ f
        q = (f ∘ ρ) ◁ δ
        first = comp-inv-right (f ◁ comp-unitˡ ρ) A ∙
          comp₌-cong (triangle-whiskered ρ f) (id₌ (A ⁻¹))
    in comp₌-cong ((right-unitor-comp ρ f) ⁻¹) (id₌ q) ∙
      ((comp₌-assoc (f ◁ comp-unitʳ ρ) C′ q) ⁻¹ ∙
      (comp₌-cong (id₌ (f ◁ comp-unitʳ ρ)) ((postWhisker-comp-One δ ρ f) ⁻¹) ∙
      (comp₌-assoc (f ◁ comp-unitʳ ρ) (f ◁ (ρ ◁ δ)) B ∙
      (comp₌-cong
        (postWhisker-comp₌ f (comp-unitʳ ρ) (ρ ◁ δ) ∙
          ((postWhisker f ◁ unit-triangle ⁻¹) ∙
            (postWhisker-comp₌ f (comp-unitˡ ρ) bJ) ⁻¹)) (id₌ B) ∙
      ((comp₌-assoc (f ◁ comp-unitˡ ρ) (f ◁ bJ) B) ⁻¹ ∙
      (comp₌-cong first (id₌ ((f ◁ bJ) ∙ B)) ∙
        (comp₌-assoc (comp-unitʳ f ▷ ρ) (A ⁻¹) ((f ◁ bJ) ∙ B)) ⁻¹))))))

  restrict-triangle-right-unit : {R K C : CAT Γ}
    (π : MAP K C) (h : MAP R K) (F : MAP R C) (b : (π ∘ h) =₁ F)
    (J : MAP R R) (δ : J =₁ (id R))
    → (b ∙ (π ◁ (comp-unitʳ h ∙ (h ◁ δ)))) =₂
        (comp-unitʳ F ∙ ((F ◁ δ) ∙ restrict-triangle π h b J))
  restrict-triangle-right-unit π h F b J δ =
    let A = comp-assoc (id _) h π
        solved = (comp-inv-right (π ◁ comp-unitʳ h) A ∙
          comp₌-cong (right-unitor-comp h π) (id₌ (A ⁻¹))) ⁻¹
        head = comp₌-assoc (comp-unitʳ F) (b ▷ id _) (A ⁻¹) ∙
          (comp₌-cong ((preWhisker-id-One b) ⁻¹) (id₌ (A ⁻¹)) ∙
          ((comp₌-assoc b (comp-unitʳ (π ∘ h)) (A ⁻¹)) ⁻¹ ∙
            comp₌-cong (id₌ b) solved))
    in comp₌-cong (id₌ (comp-unitʳ F)) (restrict-change-square-One π h F b δ) ∙
      (comp₌-assoc (comp-unitʳ F) ((b ▷ id _) ∙ A ⁻¹) (π ◁ (h ◁ δ)) ∙
      (comp₌-cong head (id₌ (π ◁ (h ◁ δ))) ∙
        project-composite π (comp-unitʳ h) (h ◁ δ) b))

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    right-unit-projection : {K C : CAT Γ}
      (ρ : MAP R X) (x : Term C) (π : MAP K C) (h h′ : MAP R K)
      (J : MAP R R) (δ : J =₁ (id R))
      (b : (π ∘ h) =₁ (x ∘ ρ))
      (b′ : (π ∘ h′) =₁ ((x ∘ id X) ∘ ρ))
      (bJ : (ρ ∘ J) =₁ (id X ∘ ρ))
      (out : h′ =₁ h) (step : (h ∘ J) =₁ h′)
      → (comp-unitʳ ρ ∙ (ρ ◁ δ)) =₂ (comp-unitˡ ρ ∙ bJ)
      → (b ∙ (π ◁ out)) =₂ ((comp-unitʳ x ▷ ρ) ∙ b′)
      → (b′ ∙ (π ◁ step)) =₂
          (post-square-cell x ρ (id X) ρ J bJ ∙ restrict-triangle π h b J)
      → (π ◁ (out ∙ step)) =₂ (π ◁ (comp-unitʳ h ∙ (h ◁ δ)))
    right-unit-projection ρ x π h h′ J δ b b′ bJ out step unit-triangle out-triangle step-triangle =
      let e = post-square-cell x ρ (id _) ρ J bJ
          left-normal = projected-triangles
            b (π ◁ out) (π ◁ step) (comp-unitʳ x ▷ ρ) b′
            e (restrict-triangle π h b J) (comp-unitʳ (x ∘ ρ)) ((x ∘ ρ) ◁ δ)
            (b ∙ (π ◁ (out ∙ step)))
            (project-composite π out step b) out-triangle step-triangle
            (post-square-cell-right-unit ρ x J δ bJ unit-triangle)
      in cancel-left b
        ((restrict-triangle-right-unit π h (x ∘ ρ) b J δ) ⁻¹ ∙ left-normal)
```

## An identification of an endofunctor with the identity

If `η : H = id` satisfies the unit triangle against a supplied `b : π ∘ H = π`,
then its postcompositions and restrictions satisfy the corresponding
triangles. (Formerly `eta-post-coordinate` and `eta-pre-coordinate`.)

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    identity-post-coordinate : {A B : CAT Γ} (π : Term A) (F : MAP A B)
      (H : Term X) (η : H =₁ (id X)) (b : (π ∘ H) =₁ π)
      → (comp-unitʳ π ∙ (π ◁ η)) =₂ b
      → (comp-unitʳ (F ∘ π) ∙ ((F ∘ π) ◁ η)) =₂ post-triangle F π H b
    identity-post-coordinate π F H η b triangle =
      comp₌-cong (postWhisker F ◁ triangle) (id₌ (comp-assoc H π F)) ∙
      (comp₌-cong ((postWhisker-comp₌ F (comp-unitʳ π) (π ◁ η)) ⁻¹)
          (id₌ (comp-assoc H π F)) ∙
      ((comp₌-assoc (F ◁ comp-unitʳ π) (F ◁ (π ◁ η)) (comp-assoc H π F)) ⁻¹ ∙
      (comp₌-cong (id₌ (F ◁ comp-unitʳ π)) (postWhisker-comp-One η π F) ∙
      (comp₌-assoc (F ◁ comp-unitʳ π) (comp-assoc (id _) π F) ((F ∘ π) ◁ η) ∙
        comp₌-cong (right-unitor-comp π F) (id₌ ((F ∘ π) ◁ η))))))

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    identity-pre-coordinate : {C : CAT Γ} (π : Term C) (s : MAP R X)
      (H : Term X) (η : H =₁ (id X)) (b : (π ∘ H) =₁ π)
      → (comp-unitʳ π ∙ (π ◁ η)) =₂ b
      → (π ◁ (comp-unitˡ s ∙ (η ▷ s))) =₂ restrict-triangle π H b s
    identity-pre-coordinate π s H η b triangle =
      let A = comp-assoc s (id _) π
          triangle-solved = (comp-inv-right (π ◁ comp-unitˡ s) A ∙
            comp₌-cong (triangle-whiskered s π) (id₌ (A ⁻¹))) ⁻¹
          square = restrict-square-One π η (id₌ π) b (comp-unitʳ π) s
            ((comp₌-unitˡ-One b) ⁻¹ ∙ triangle)
          tail = restrict-triangle π H b s
      in comp₌-unitˡ-One tail ∙
        (comp₌-cong (preWhisker-id₌ π s) (id₌ tail) ∙
        (square ∙
        (comp₌-cong triangle-solved (id₌ (π ◁ (η ▷ s))) ∙
          postWhisker-comp₌ π (comp-unitˡ s) (η ▷ s))))
```

## Identifications lying over identifications

A square `SquareCell₌ (π ◁ ε) α b b′` says that `ε` lies over `α` with
respect to the triangles `b` and `b′` (constant families of triangles for a
family `ε`, the triangles themselves for an individual identification).
Composites of identifications lying over `α₁` and `α₂` lie over `α₂ ∙ α₁`,
inverses lie over inverses, and an identity lies over an identity. These are
the operations used to recognize an identification into a product by its
projections, and identifications between functors over a base.

```agda
module _ {Γ : Context} where
  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities A using (_＝_)

    lies-over-comp : {K C : CAT Γ} (π : MAP K C)
      {h₀ h₁ h₂ : Term K} {z₀ z₁ z₂ : Term C}
      {b₀ : ((π ∘ h₀) ＝ z₀)} {b₁ : ((π ∘ h₁) ＝ z₁)} {b₂ : ((π ∘ h₂) ＝ z₂)}
      {ε₂ : h₁ ＝ h₂} {ε₁ : h₀ ＝ h₁}
      {α₂ : z₁ ＝ z₂} {α₁ : z₀ ＝ z₁}
      → SquareCell₌ (π ◁ ε₁) α₁ b₀ b₁
      → SquareCell₌ (π ◁ ε₂) α₂ b₁ b₂
      → SquareCell₌ (π ◁ (ε₂ ∙ ε₁)) (α₂ ∙ α₁) b₀ b₂
    lies-over-comp π {ε₂ = ε₂} {ε₁} {α₂} {α₁} first second =
      replace-edges₌ ((postWhisker-comp₌ π ε₂ ε₁) ⁻¹) (id₌ (α₂ ∙ α₁))
        (adjoin-square₌ first second)

    lies-over-inverse : {K C : CAT Γ} (π : MAP K C)
      {h h′ : Term K} {z z′ : Term C}
      {b : ((π ∘ h) ＝ z)} {b′ : ((π ∘ h′) ＝ z′)}
      {ε : h ＝ h′} {α : z ＝ z′}
      → SquareCell₌ (π ◁ ε) α b b′
      → SquareCell₌ (π ◁ ε ⁻¹) (α ⁻¹) b′ b
    lies-over-inverse π {b = b} {b′} {ε} {α} square =
      replace-edges₌ ((postWhisker-inverse π ε) ⁻¹) (id₌ (α ⁻¹))
        (transpose-square₌ (inverse-square₌ {t = b} {b = b′} {l = π ◁ ε} {r = α}
          (transpose-square₌ square)))
```

Lying over is invariant under a change of frame: if `ε` lies over `α` along
`π`, and `v : q = π`, then `ε` lies over `α` along `q`, with the triangles
precomposed by the restrictions of `v`. The required square of the two
projections of `ε` is the interchange law.

```agda
    lies-over-reframe : {K C : CAT Γ} {π q : MAP K C} (v : q ＝ π)
      {h h′ : Term K} {z z′ : Term C}
      {b : ((π ∘ h) ＝ z)} {b′ : ((π ∘ h′) ＝ z′)}
      {ε : h ＝ h′} {α : z ＝ z′}
      → SquareCell₌ (π ◁ ε) α b b′
      → SquareCell₌ (q ◁ ε) α (b ∙ (v ▷ h)) (b′ ∙ (v ▷ h′))
    lies-over-reframe {π = π} {q} v {ε = ε} {α} square =
      paste-square₌ {t = q ◁ ε} {m = π ◁ ε} {b = α} (interchange v ε) square

  module _ {A X : CAT Γ} where
    open Terms.InContext X using (Term)

    lies-over-id : {K C : CAT Γ} (π : MAP K C) {h : Term K} {z : Term C}
      (b : (π ∘ h) =₁ z)
      → SquareCell₌ (π ◁ const {P = A} (id₌ h)) (const (id₌ z)) (const b) (const b)
    lies-over-id  π {h} b =
      replace-edges₌
        ((const-cong {X = A} (postWhisker-id₌ π h) ∙ post-constant π (id₌ h)) ⁻¹)
        (id₌ (const (id₌ _)))
        (transpose-square₌ (identity-square₌ (const {P = A} b)))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    lies-over-id-One : {K C : CAT Γ} (π : MAP K C) {h : Term K} {z : Term C}
      (b : (π ∘ h) =₁ z)
      → SquareCell₌ (π ◁ id₌ h) (id₌ z) b b
    lies-over-id-One π {h} {z} b =
      replace-edges₌ ((postWhisker-id₌ π h) ⁻¹ ∙ const-One (id₌ (π ∘ h))) (const-One (id₌ z))
        (transpose-square₌ (identity-square₌ b))
```
