# Squares between functors

The two horizontal functors `f` and `f′` are fixed in the type. The side
functors and the commuting identification are data. These squares are
distinct from squares whose edges are identification families
(Section03.Identifications.IdentificationSquares).

Squares compose by pasting, and `SquareEquality` identifies two squares
with the same horizontal functors. The second half of this file is the
calculus of these identifications: they can be inverted and composed,
pasting respects them, and pasting is unital and associative up to them.
The unit and associativity laws use Kelly's lemmas and the whiskered
pentagon (Section03.Identifications.FunctorCoherence).

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Squares where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌;
    module Composition; module Boundaries)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open Operations
open Composition
open Boundaries using (SquareCell₌)

module _ {Γ : Context} where
  record Square {A B A′ B′ : CAT Γ} (f : MAP A B) (f′ : MAP A′ B′) : Set m where
    constructor square
    field
      source-map : MAP A A′
      target-map : MAP B B′
      cell : (f′ ∘ source-map) =₁ (target-map ∘ f)

  id-square : {A B : CAT Γ} (f : MAP A B) → Square f f
  id-square {A} {B} f = square (id A) (id B)
    ((comp-unitˡ f) ⁻¹ ∙ comp-unitʳ f)

  comp-square : {A B A′ B′ A″ B″ : CAT Γ}
    {f : MAP A B} {f′ : MAP A′ B′} {f″ : MAP A″ B″}
    → Square f′ f″ → Square f f′ → Square f f″
  comp-square {f = f} {f′} {f″} Q P =
    square (source-map Q ∘ source-map P) (target-map Q ∘ target-map P)
      ((comp-assoc f (target-map P) (target-map Q)) ⁻¹ ∙
        ((target-map Q ◁ cell P) ∙
          (comp-assoc (source-map P) f′ (target-map Q) ∙
            ((cell Q ▷ source-map P) ∙
              (comp-assoc (source-map P) (source-map Q) f″) ⁻¹))))
    where open Square
```

## Squares with all four boundaries fixed

`FunctorSquare C D C′ D′` packages all four edges of a square and its cell,
with no edge fixed in the type. It is the same data as `Square`, with the
side functors of a `Square f f′` as the top and bottom edges; the two views
are mutually inverse by definition. Later sections use it where all four
edges vary together.

```agda
module _ {Γ : Context} where
  record FunctorSquare (C D C′ D′ : CAT Γ) : Set m where
    constructor functor-square-data
    field
      top : MAP C D
      left : MAP C C′
      right : MAP D D′
      bottom : MAP C′ D′
      cell : (right ∘ top) =₁ (bottom ∘ left)

  functor-square : {A B A′ B′ : CAT Γ} {f : MAP A B} {f′ : MAP A′ B′}
    → Square f f′ → FunctorSquare A A′ B B′
  functor-square {f = f} {f′} P =
    functor-square-data (Square.source-map P) f f′ (Square.target-map P) (Square.cell P)

  from-functor-square : {C D C′ D′ : CAT Γ} (s : FunctorSquare C D C′ D′)
    → Square (FunctorSquare.left s) (FunctorSquare.right s)
  from-functor-square s = square (FunctorSquare.top s) (FunctorSquare.bottom s) (FunctorSquare.cell s)
```

## Identifications between squares

`SquareEquality` supplies identifications of both side functors and a
specified compatibility between the two square cells. It is synthetic
identification data, not Agda equality of records. Its equation is the
commutativity of the identification square whose top and bottom edges are
the two cells and whose sides are the whiskered side identifications.

```agda
  record SquareEquality {A B A′ B′ : CAT Γ}
    {f : MAP A B} {f′ : MAP A′ B′} (P Q : Square f f′) : Set m where
    field
      source-identification : Square.source-map P =₁ Square.source-map Q
      target-identification : Square.target-map P =₁ Square.target-map Q
      compatibility : ((target-identification ▷ f) ∙ Square.cell P) =₂
        (Square.cell Q ∙ (f′ ◁ source-identification))

  square-equality-cell : {A B A′ B′ : CAT Γ} {f : MAP A B} {f′ : MAP A′ B′}
    {P Q : Square f f′} (E : SquareEquality P Q)
    → SquareCell₌ (Square.cell P) (Square.cell Q)
        (f′ ◁ SquareEquality.source-identification E)
        (SquareEquality.target-identification E ▷ f)
  square-equality-cell E = SquareEquality.compatibility E
```

## Reflexivity, inversion and composition

Every square is identified with itself by the identity identifications of
its sides; whiskering preserves identity identifications, and the unit laws
remove them. The inverse identifies the sides by the inverse
identifications; its compatibility is the inverted identification square.
Composition composes the side identifications; its compatibility pastes the
two identification squares along the middle cell.

```agda
  square-equality-refl : {A B A′ B′ : CAT Γ} {f : MAP A B} {f′ : MAP A′ B′}
    (P : Square f f′) → SquareEquality P P
  square-equality-refl {f = f} {f′} P =
    let s = Square.source-map P
        t = Square.target-map P
        c = Square.cell P
    in record
      { source-identification = id₌ s
      ; target-identification = id₌ t
      ; compatibility =
          (comp₌-cong (id₌ c) (postWhisker-id₌ f′ s)) ⁻¹ ∙ ((comp₌-unitʳ-One c) ⁻¹ ∙
            (comp₌-unitˡ-One c ∙ comp₌-cong (preWhisker-id₌ t f) (id₌ c)))
      }

  square-equality-sym : {A B A′ B′ : CAT Γ} {f : MAP A B} {f′ : MAP A′ B′}
    {P Q : Square f f′} → SquareEquality P Q → SquareEquality Q P
  square-equality-sym {f = f} {f′} {P} {Q} E = record
    { source-identification = s ⁻¹
    ; target-identification = t ⁻¹
    ; compatibility = replace-sides₌
        ((postWhisker-inverse f′ s) ⁻¹) ((preWhisker-inverse t f) ⁻¹)
        (inverse-square₌ {t = Square.cell P} {b = Square.cell Q}
          {l = f′ ◁ s} {r = t ▷ f} (square-equality-cell E))
    }
    where
    s = SquareEquality.source-identification E
    t = SquareEquality.target-identification E

  square-equality-trans : {A B A′ B′ : CAT Γ} {f : MAP A B} {f′ : MAP A′ B′}
    {P Q R : Square f f′} → SquareEquality P Q → SquareEquality Q R → SquareEquality P R
  square-equality-trans {f = f} {f′} {P} {Q} {R} E F = record
    { source-identification = s₂ ∙ s₁
    ; target-identification = t₂ ∙ t₁
    ; compatibility = replace-sides₌
        ((postWhisker-comp₌ f′ s₂ s₁) ⁻¹) ((preWhisker-comp₌ t₂ t₁ f) ⁻¹)
        (paste-square₌ {t = Square.cell P} {m = Square.cell Q} {b = Square.cell R}
          (square-equality-cell E) (square-equality-cell F))
    }
    where
    s₁ = SquareEquality.source-identification E
    t₁ = SquareEquality.target-identification E
    s₂ = SquareEquality.source-identification F
    t₂ = SquareEquality.target-identification F
```

## Pasting respects identifications of squares

Changing the outer square of a pasting by a `SquareEquality` changes the
pasted square, with the side identifications whiskered by the inner side
functors; dually for the inner square. Each compatibility is the vertical
pasting of five identification squares, one for each factor of the pasted
cell: an associator square, the given compatibility (whiskered), an
associator square, an interchange or whiskered square, and an associator
square. Changing both squares composes the two, so that the sides become
the horizontal composites `θ ⋆ η` and `ψ ⋆ φ` of the side identifications.

```agda
module _ {Γ : Context} where
  comp-square-congˡ : {A B A′ B′ A″ B″ : CAT Γ}
    {f : MAP A B} {f′ : MAP A′ B′} {f″ : MAP A″ B″}
    {Q Q′ : Square f′ f″} → SquareEquality Q Q′ → (P : Square f f′)
    → SquareEquality (comp-square Q P) (comp-square Q′ P)
  comp-square-congˡ {f = x₀} {x₁} {x₂} {Q} {Q′} E P =
    let open Square
        g = source-map Q
        g′ = source-map Q′
        G = target-map Q
        G′ = target-map Q′
        β = cell Q
        β′ = cell Q′
        f = source-map P
        F = target-map P
        α = cell P
        θ = SquareEquality.source-identification E
        ψ = SquareEquality.target-identification E
        first : SquareCell₌ (x₂ ◁ (θ ▷ f)) ((x₂ ◁ θ) ▷ f)
          ((comp-assoc f g x₂) ⁻¹) ((comp-assoc f g′ x₂) ⁻¹)
        first = inverse-square₌ {t = (x₂ ◁ θ) ▷ f} {b = x₂ ◁ (θ ▷ f)}
          {l = comp-assoc f g x₂} {r = comp-assoc f g′ x₂} (whisker-mixed-One θ f x₂)
        second : SquareCell₌ ((x₂ ◁ θ) ▷ f) ((ψ ▷ x₁) ▷ f) (β ▷ f) (β′ ▷ f)
        second = pre-square₌ f {t = x₂ ◁ θ} {b = ψ ▷ x₁} {l = β} {r = β′}
          ((square-equality-cell E) ⁻¹)
        third : SquareCell₌ ((ψ ▷ x₁) ▷ f) (ψ ▷ (x₁ ∘ f))
          (comp-assoc f x₁ G) (comp-assoc f x₁ G′)
        third = preWhisker-comp-One ψ x₁ f
        fourth : SquareCell₌ (ψ ▷ (x₁ ∘ f)) (ψ ▷ (F ∘ x₀)) (G ◁ α) (G′ ◁ α)
        fourth = (interchange ψ α) ⁻¹
        fifth : SquareCell₌ (ψ ▷ (F ∘ x₀)) ((ψ ▷ F) ▷ x₀)
          ((comp-assoc x₀ F G) ⁻¹) ((comp-assoc x₀ F G′) ⁻¹)
        fifth = inverse-square₌ {t = (ψ ▷ F) ▷ x₀} {b = ψ ▷ (F ∘ x₀)}
          {l = comp-assoc x₀ F G} {r = comp-assoc x₀ F G′} (preWhisker-comp-One ψ F x₀)
        pasted = paste-square₌ (paste-square₌ (paste-square₌ (paste-square₌
          first second) third) fourth) fifth
    in record
      { source-identification = θ ▷ f
      ; target-identification = ψ ▷ F
      ; compatibility = pasted ⁻¹
      }

  comp-square-congʳ : {A B A′ B′ A″ B″ : CAT Γ}
    {f : MAP A B} {f′ : MAP A′ B′} {f″ : MAP A″ B″}
    (Q : Square f′ f″) {P P′ : Square f f′} → SquareEquality P P′
    → SquareEquality (comp-square Q P) (comp-square Q P′)
  comp-square-congʳ {f = x₀} {x₁} {x₂} Q {P} {P′} E =
    let open Square
        g = source-map Q
        G = target-map Q
        β = cell Q
        f = source-map P
        f′ = source-map P′
        F = target-map P
        F′ = target-map P′
        α = cell P
        α′ = cell P′
        η = SquareEquality.source-identification E
        φ = SquareEquality.target-identification E
        first : SquareCell₌ (x₂ ◁ (g ◁ η)) ((x₂ ∘ g) ◁ η)
          ((comp-assoc f g x₂) ⁻¹) ((comp-assoc f′ g x₂) ⁻¹)
        first = inverse-square₌ {t = (x₂ ∘ g) ◁ η} {b = x₂ ◁ (g ◁ η)}
          {l = comp-assoc f g x₂} {r = comp-assoc f′ g x₂} (postWhisker-comp-One η g x₂)
        second : SquareCell₌ ((x₂ ∘ g) ◁ η) ((G ∘ x₁) ◁ η) (β ▷ f) (β ▷ f′)
        second = interchange β η
        third : SquareCell₌ ((G ∘ x₁) ◁ η) (G ◁ (x₁ ◁ η))
          (comp-assoc f x₁ G) (comp-assoc f′ x₁ G)
        third = postWhisker-comp-One η x₁ G
        fourth : SquareCell₌ (G ◁ (x₁ ◁ η)) (G ◁ (φ ▷ x₀)) (G ◁ α) (G ◁ α′)
        fourth = post-square₌ G {t = x₁ ◁ η} {b = φ ▷ x₀} {l = α} {r = α′}
          ((square-equality-cell E) ⁻¹)
        fifth : SquareCell₌ (G ◁ (φ ▷ x₀)) ((G ◁ φ) ▷ x₀)
          ((comp-assoc x₀ F G) ⁻¹) ((comp-assoc x₀ F′ G) ⁻¹)
        fifth = inverse-square₌ {t = (G ◁ φ) ▷ x₀} {b = G ◁ (φ ▷ x₀)}
          {l = comp-assoc x₀ F G} {r = comp-assoc x₀ F′ G} (whisker-mixed-One φ x₀ G)
        pasted = paste-square₌ (paste-square₌ (paste-square₌ (paste-square₌
          first second) third) fourth) fifth
    in record
      { source-identification = g ◁ η
      ; target-identification = G ◁ φ
      ; compatibility = pasted ⁻¹
      }

  comp-square-cong : {A B A′ B′ A″ B″ : CAT Γ}
    {f : MAP A B} {f′ : MAP A′ B′} {f″ : MAP A″ B″}
    {Q Q′ : Square f′ f″} {P P′ : Square f f′}
    → SquareEquality Q Q′ → SquareEquality P P′
    → SquareEquality (comp-square Q P) (comp-square Q′ P′)
  comp-square-cong {Q = Q} {P′ = P′} E F =
    square-equality-trans (comp-square-congʳ Q F) (comp-square-congˡ E P′)
```

The pasted cell is a postcomposed cell followed by a restricted triangle.

```agda
  comp-square-cell-factor : {A B A′ B′ A″ B″ : CAT Γ}
    {f : MAP A B} {f′ : MAP A′ B′} {f″ : MAP A″ B″}
    (Q : Square f′ f″) (P : Square f f′)
    → Square.cell (comp-square Q P) =₂
        (post-square-cell (Square.target-map Q) f (Square.target-map P) f′
          (Square.source-map P) (Square.cell P) ∙
          restrict-triangle f″ (Square.source-map Q) (Square.cell Q) (Square.source-map P))
  comp-square-cell-factor {f = x₀} {x₁} {x₂} Q P =
    let open Square
        G = target-map Q
        F = target-map P
        f = source-map P
        tail = restrict-triangle x₂ (source-map Q) (cell Q) f
    in (comp₌-assoc ((comp-assoc x₀ F G) ⁻¹) ((G ◁ cell P) ∙ comp-assoc f x₁ G) tail) ⁻¹ ∙
      comp₌-cong (id₌ ((comp-assoc x₀ F G) ⁻¹))
        ((comp₌-assoc (G ◁ cell P) (comp-assoc f x₁ G) tail) ⁻¹)
```

## Units of pasting

Pasting with an identity square is identified with the original square by
the unitors of the side functors. The unit laws use Kelly's lemmas; in
particular the identity retract below is an instance.

```agda
module _ {Γ : Context} where
  comp-square-unitʳ : {A B A′ B′ : CAT Γ} {x : MAP A B} {y : MAP A′ B′}
    (P : Square x y) → SquareEquality (comp-square P (id-square x)) P
  comp-square-unitʳ {A} {x = x} {y} P =
    let f = Square.source-map P
        F = Square.target-map P
        α = Square.cell P
        u = comp-unitʳ F ▷ x
        A₀ = comp-assoc x (id _) F
        B₀ = F ◁ Square.cell (id-square x)
        C₀ = comp-assoc (id A) x F
        D₀ = α ▷ id A
        E₀ = (comp-assoc (id A) f y) ⁻¹
        head = comp-inv-right (F ◁ comp-unitˡ x) A₀ ∙
          comp₌-cong (triangle-whiskered x F) (id₌ (A₀ ⁻¹))
        middle = (postWhisker F ◁ comp-inv-left (comp-unitˡ x) (comp-unitʳ x)) ∙
          (postWhisker-comp₌ F (comp-unitˡ x) (Square.cell (id-square x))) ⁻¹
        finish = comp-inv-right (y ◁ comp-unitʳ f) (comp-assoc (id A) f y) ∙
          comp₌-cong (right-unitor-comp f y) (id₌ E₀)
    in record
      { source-identification = comp-unitʳ f
      ; target-identification = comp-unitʳ F
      ; compatibility = comp₌-cong (id₌ α) finish ∙
          (comp₌-assoc α (comp-unitʳ (y ∘ f)) E₀ ∙
          (comp₌-cong (preWhisker-id-One α) (id₌ E₀) ∙
          ((comp₌-assoc (comp-unitʳ (F ∘ x)) D₀ E₀) ⁻¹ ∙
          (comp₌-cong ((right-unitor-comp x F) ⁻¹) (id₌ (D₀ ∙ E₀)) ∙
          ((comp₌-assoc (F ◁ comp-unitʳ x) C₀ (D₀ ∙ E₀)) ⁻¹ ∙
          (comp₌-cong middle (id₌ (C₀ ∙ (D₀ ∙ E₀))) ∙
          ((comp₌-assoc (F ◁ comp-unitˡ x) B₀ (C₀ ∙ (D₀ ∙ E₀))) ⁻¹ ∙
          (comp₌-cong head (id₌ (B₀ ∙ (C₀ ∙ (D₀ ∙ E₀)))) ∙
            (comp₌-assoc u (A₀ ⁻¹) (B₀ ∙ (C₀ ∙ (D₀ ∙ E₀)))) ⁻¹))))))))
      }

  comp-square-unitˡ : {A B A′ B′ : CAT Γ} {x : MAP A B} {y : MAP A′ B′}
    (P : Square x y) → SquareEquality (comp-square (id-square y) P) P
  comp-square-unitˡ {B′ = B′} {x = x} {y} P =
    let f = Square.source-map P
        F = Square.target-map P
        α = Square.cell P
        u = comp-unitˡ F ▷ x
        A₀ = comp-assoc x F (id B′)
        B₀ = id B′ ◁ α
        C₀ = comp-assoc f y (id B′)
        D₀ = Square.cell (id-square y) ▷ f
        E₀ = (comp-assoc f (id _) y) ⁻¹
        head = comp-inv-right (comp-unitˡ (F ∘ x)) A₀ ∙
          comp₌-cong ((left-unitor-comp x F) ⁻¹) (id₌ (A₀ ⁻¹))
        middle = (preWhisker f ◁ comp-inv-left (comp-unitˡ y) (comp-unitʳ y)) ∙
          (preWhisker-comp₌ (comp-unitˡ y) (Square.cell (id-square y)) f) ⁻¹
        finish = comp-inv-right (y ◁ comp-unitˡ f) (comp-assoc f (id _) y) ∙
          comp₌-cong (triangle-whiskered f y) (id₌ E₀)
        tail = finish ∙
          (comp₌-cong middle (id₌ E₀) ∙
          ((comp₌-assoc (comp-unitˡ y ▷ f) D₀ E₀) ⁻¹ ∙
          (comp₌-cong (left-unitor-comp f y) (id₌ (D₀ ∙ E₀)) ∙
            (comp₌-assoc (comp-unitˡ (y ∘ f)) C₀ (D₀ ∙ E₀)) ⁻¹)))
    in record
      { source-identification = comp-unitˡ f
      ; target-identification = comp-unitˡ F
      ; compatibility = comp₌-cong (id₌ α) tail ∙
          (comp₌-assoc α (comp-unitˡ (y ∘ f)) (C₀ ∙ (D₀ ∙ E₀)) ∙
          (comp₌-cong (postWhisker-id-One α) (id₌ (C₀ ∙ (D₀ ∙ E₀))) ∙
          ((comp₌-assoc (comp-unitˡ (F ∘ x)) B₀ (C₀ ∙ (D₀ ∙ E₀))) ⁻¹ ∙
          (comp₌-cong head (id₌ (B₀ ∙ (C₀ ∙ (D₀ ∙ E₀)))) ∙
            (comp₌-assoc u (A₀ ⁻¹) (B₀ ∙ (C₀ ∙ (D₀ ∙ E₀)))) ⁻¹))))
      }
```

## Associativity of pasting

Pasting is associative up to the associators of the side functors. Factor
both pasted cells; then compare successive postcomposition of the inner
cell (`post-square-cell-comp`) and successive restriction of the outer
triangles (`restrict-triangle-assoc`), each a whiskered pentagon.

```agda
module _ {Γ : Context} where
  private
    post-cancel-inverse : {X Y Z : CAT Γ} (F : MAP Y Z) {u v : MAP X Y}
      (β : u =₁ v) {w : MAP X Z} (α : w =₁ (F ∘ v))
      → ((F ◁ β) ∙ ((F ◁ β ⁻¹) ∙ α)) =₂ α
    post-cancel-inverse F β α = comp-inv-left (F ◁ β) α ∙
      comp₌-cong (id₌ (F ◁ β)) (comp₌-cong (postWhisker-inverse F β) (id₌ α))

    pre-cancel-inverse : {R X Y : CAT Γ} {u v w : MAP X Y}
      (β : v =₁ w) (α : u =₁ w) (r : MAP R X)
      → ((β ▷ r) ∙ ((β ⁻¹ ∙ α) ▷ r)) =₂ (α ▷ r)
    pre-cancel-inverse β α r = (preWhisker r ◁ comp-inv-left β α) ∙
      (preWhisker-comp₌ β (β ⁻¹ ∙ α) r) ⁻¹

    restrict-paste : {A₀ A₁ A₂ A₃ B₁ B₂ B₃ : CAT Γ}
      (f : MAP A₀ A₁) {g : MAP A₁ A₂} {h : MAP A₂ A₃}
      {G : MAP B₁ B₂} {H : MAP B₂ B₃}
      {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂} {x₃ : MAP A₃ B₃}
      (γ : (x₃ ∘ h) =₁ (H ∘ x₂)) (β : (x₂ ∘ g) =₁ (G ∘ x₁))
      → (comp-assoc f (G ∘ x₁) H ∙
          ((comp-assoc x₁ G H ▷ f) ∙
            restrict-triangle x₃ (h ∘ g)
              (Square.cell (comp-square (square h H γ) (square g G β))) f)) =₂
        ((H ◁ restrict-triangle x₂ g β f) ∙
          (comp-assoc (g ∘ f) x₂ H ∙
            (restrict-triangle x₃ h γ (g ∘ f) ∙ (x₃ ◁ comp-assoc f g h))))
    restrict-paste f {g} {h} {G} {H} {x₁} {x₂} {x₃} γ β =
      let A = comp-assoc f (G ∘ x₁) H
          B = comp-assoc x₁ G H
          C = comp-assoc g x₂ H
          T = restrict-triangle x₃ h γ g
          tail = (comp-assoc f (h ∘ g) x₃) ⁻¹
          S = (H ◁ β) ∙ (C ∙ T)
          paste = Square.cell (comp-square (square h H γ) (square g G β))
          β′ = (H ◁ β) ▷ f
          C′ = C ▷ f
          T′ = T ▷ f
          βImage = H ◁ (β ▷ f)
          middle = comp-assoc f (x₂ ∘ g) H
          inputA = comp-assoc f g x₂
          nextA = comp-assoc (g ∘ f) x₂ H
          endA = comp-assoc f g (H ∘ x₂)
          end = restrict-triangle x₃ h γ (g ∘ f) ∙ (x₃ ◁ comp-assoc f g h)
          pentagon-right : (nextA ∙ endA) =₂ ((H ◁ inputA) ∙ (middle ∙ C′))
          pentagon-right = comp₌-assoc (H ◁ inputA) middle C′ ∙ pentagon-whiskered f g x₂ H
          corner = cancel-left (H ◁ inputA)
            ((post-cancel-inverse H inputA (nextA ∙ endA)) ⁻¹ ∙ pentagon-right ⁻¹)
          transport = restrict-triangle-twice x₃ h γ g f
          expandS = comp₌-cong (id₌ β′) (preWhisker-comp₌ C T f) ∙
            preWhisker-comp₌ (H ◁ β) (C ∙ T) f
          cancelB = comp₌-cong (pre-cancel-inverse B S f) (id₌ tail) ∙
            (comp₌-assoc (B ▷ f) (paste ▷ f) tail) ⁻¹
          expand = comp₌-cong (id₌ A)
            (comp₌-cong (id₌ β′) (comp₌-assoc C′ T′ tail) ∙
              (comp₌-assoc β′ (C′ ∙ T′) tail ∙
                comp₌-cong expandS (id₌ tail)))
          firstExchange = comp₌-cong (whisker-mixed-One β f H) (id₌ (C′ ∙ (T′ ∙ tail))) ∙
            (comp₌-assoc A β′ (C′ ∙ (T′ ∙ tail))) ⁻¹
          secondExchange = comp₌-assoc βImage middle (C′ ∙ (T′ ∙ tail))
          useCorner = comp₌-cong (id₌ βImage)
            (comp₌-cong corner (id₌ (T′ ∙ tail)) ∙
              (comp₌-assoc middle C′ (T′ ∙ tail)) ⁻¹)
          finishTail = comp₌-cong (id₌ βImage)
            (comp₌-cong (id₌ (H ◁ inputA ⁻¹))
                (comp₌-cong (id₌ nextA)
                    (transport ∙ (comp₌-assoc endA T′ tail) ⁻¹) ∙
                  comp₌-assoc nextA endA (T′ ∙ tail)) ∙
              comp₌-assoc (H ◁ inputA ⁻¹) (nextA ∙ endA) (T′ ∙ tail))
      in comp₌-cong ((postWhisker-comp₌ H (β ▷ f) (inputA ⁻¹)) ⁻¹) (id₌ (nextA ∙ end)) ∙
        ((comp₌-assoc βImage (H ◁ inputA ⁻¹) (nextA ∙ end)) ⁻¹ ∙
        (finishTail ∙ (useCorner ∙ (secondExchange ∙ (firstExchange ∙
          (expand ∙ comp₌-cong (id₌ A) cancelB))))))

  comp-square-assoc : {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : CAT Γ}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂} {x₃ : MAP A₃ B₃}
    (R : Square x₂ x₃) (Q : Square x₁ x₂) (P : Square x₀ x₁)
    → SquareEquality (comp-square (comp-square R Q) P) (comp-square R (comp-square Q P))
  comp-square-assoc {x₀ = x₀} {x₁} {x₂} {x₃} R Q P =
    let open Square
        f = source-map P
        F = target-map P
        α = cell P
        g = source-map Q
        G = target-map Q
        β = cell Q
        h = source-map R
        H = target-map R
        γ = cell R
        c = post-square-cell G x₀ F x₁ f α
        cHG = post-square-cell (H ∘ G) x₀ F x₁ f α
        nested = post-square-cell H x₀ (G ∘ F) (G ∘ x₁) f c
        lead = comp-assoc F G H ▷ x₀
        B = comp-assoc x₁ G H ▷ f
        t = restrict-triangle x₃ (h ∘ g) (cell (comp-square R Q)) f
        tβ = restrict-triangle x₂ g β f
        tγ = restrict-triangle x₃ h γ (g ∘ f)
        last = x₃ ◁ comp-assoc f g h
        I = (comp-assoc x₀ (G ∘ F) H) ⁻¹
        A = comp-assoc f (G ∘ x₁) H
        N = comp-assoc (g ∘ f) x₂ H
        hc = H ◁ c
        hβ = H ◁ tβ
        hp = H ◁ cell (comp-square Q P)
        start = comp₌-cong (id₌ lead) (comp-square-cell-factor (comp-square R Q) P)
        outer = comp₌-assoc nested B t ∙
          (comp₌-cong ((post-square-cell-comp x₀ F x₁ f α G H) ⁻¹) (id₌ t) ∙
            (comp₌-assoc lead cHG t) ⁻¹)
        expand = comp₌-cong (id₌ I) (comp₌-assoc hc A (B ∙ t)) ∙
          comp₌-assoc I (hc ∙ A) (B ∙ t)
        transport = comp₌-cong (id₌ I) (comp₌-cong (id₌ hc) (restrict-paste f γ β))
        merge = comp₌-cong (id₌ I)
          (comp₌-cong
            ((postWhisker H ◁ (comp-square-cell-factor Q P) ⁻¹) ∙
              (postWhisker-comp₌ H c tβ) ⁻¹)
            (id₌ (N ∙ (tγ ∙ last))) ∙
            (comp₌-assoc hc hβ (N ∙ (tγ ∙ last))) ⁻¹)
        finish = (comp₌-assoc I (hp ∙ (N ∙ tγ)) last) ⁻¹ ∙
          (comp₌-cong (id₌ I)
            ((comp₌-assoc hp (N ∙ tγ) last) ⁻¹ ∙
              comp₌-cong (id₌ hp) ((comp₌-assoc N tγ last) ⁻¹)))
    in record
      { source-identification = comp-assoc f g h
      ; target-identification = comp-assoc F G H
      ; compatibility = finish ∙ (merge ∙ (transport ∙ (expand ∙ (outer ∙ start))))
      }
```
