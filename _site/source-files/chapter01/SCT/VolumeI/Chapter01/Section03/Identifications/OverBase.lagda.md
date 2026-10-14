# Identifications over a base

Let `X` and `Y` be categories over `S` and `F`, `G : X → Y` functors over
the base. An identification `α : functor F = functor G` is an identification
over the base when it lies over the identity of the base functor of `X`
along the two cells: `IsIdentificationOver F G α`, the square
`SquareCell₌ (map Y ◁ α) (const (id₌ (map X))) (const (cell F)) (const (cell G))`
of Triangles, stated for families with a common parameter. This is the
public language for identifications over a base. Identifications over the
base compose and invert, can be whiskered by functors over the base on
either side, contain the unitors and the associator of functors over the
base, paste along squares of functors over the base, and are preserved by
change of base. `IdentificationOver F G` packages an identification with
its compatibility.

The relative statements rest on a lower calculation for individual
identifications with prescribed triangles, without packaging functors over
a base: `CompatibleOver π bf bg α` says `bg ∙ (π ◁ α) = bf`, which is the
lying-over square with the identity as lower edge after removing a unitor.
Its composition and inversion are direct; its whiskerings are the
restriction squares of Triangles; its unitors and associator are the fixed
coherence computations from which the relative unitors and associator are
obtained (`compatible-to-over`). The cell of `comp-over G F` is
`compose-triangle`. The last part computes the projection of a pasted
square of functors along any functor.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.OverBase where

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
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Squares using (square; comp-square; module Square)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
  using (CategoryOverBase; FunctorOverBase; functor-over; id-over; comp-over; postcompose-base)
```

## Identifications over a fixed base

```agda
module _ {Γ : Context} where
  CompatibleOver : {X Y B : CAT Γ} (π : MAP Y B) {f g : MAP X Y} {q : MAP X B}
    → (π ∘ f) =₁ q → (π ∘ g) =₁ q → f =₁ g → Set m
  CompatibleOver π bf bg α = (bg ∙ (π ◁ α)) =₂ bf

  compose-triangle : {X Y Z B : CAT Γ} (π : MAP Z B)
    (g : MAP Y Z) {q : MAP Y B} (bg : (π ∘ g) =₁ q)
    (f : MAP X Y) {r : MAP X B} (bf : (q ∘ f) =₁ r)
    → (π ∘ (g ∘ f)) =₁ r
  compose-triangle π g bg f bf = bf ∙ restrict-triangle π g bg f

  abstract
    compatible-comp : {X Y B : CAT Γ} (π : MAP Y B)
      {f g h : MAP X Y} {q : MAP X B}
      (bf : (π ∘ f) =₁ q) (bg : (π ∘ g) =₁ q) (bh : (π ∘ h) =₁ q)
      (β : g =₁ h) (α : f =₁ g)
      → CompatibleOver π bg bh β → CompatibleOver π bf bg α
      → CompatibleOver π bf bh (β ∙ α)
    compatible-comp π bf bg bh β α b a = a ∙
      (comp₌-cong b (id₌ (π ◁ α)) ∙ project-composite π β α bh)

    compatible-inverse : {X Y B : CAT Γ} (π : MAP Y B)
      {f g : MAP X Y} {q : MAP X B}
      (bf : (π ∘ f) =₁ q) (bg : (π ∘ g) =₁ q) (α : f =₁ g)
      → CompatibleOver π bf bg α → CompatibleOver π bg bf (α ⁻¹)
    compatible-inverse π bf bg α compatible =
      let cancel-image = postWhisker-id₌ π _ ∙
            ((postWhisker π ◁ comp₌-inverseʳ-One α) ∙
              (postWhisker-comp₌ π α (α ⁻¹)) ⁻¹)
      in comp₌-unitʳ-One bg ∙
        (comp₌-cong (id₌ bg) cancel-image ∙
        (comp₌-assoc bg (π ◁ α) (π ◁ α ⁻¹) ∙
          comp₌-cong (compatible ⁻¹) (id₌ (π ◁ α ⁻¹))))

    compatible-pre : {X Y Z B : CAT Γ} (π : MAP Z B)
      {g g′ : MAP Y Z} {q : MAP Y B} (f : MAP X Y) {r : MAP X B}
      (bg : (π ∘ g) =₁ q) (bg′ : (π ∘ g′) =₁ q)
      (bf : (q ∘ f) =₁ r) (α : g =₁ g′)
      → CompatibleOver π bg bg′ α
      → CompatibleOver π (compose-triangle π g bg f bf)
          (compose-triangle π g′ bg′ f bf) (α ▷ f)
    compatible-pre π {g = g} {g′} {q} f bg bg′ bf α compatible =
      let first = restrict-square-One π α (id₌ q) bg bg′ f
            ((comp₌-unitˡ-One bg) ⁻¹ ∙ compatible)
          normalized = comp₌-unitˡ-One (restrict-triangle π g bg f) ∙
            comp₌-cong (preWhisker-id₌ q f) (id₌ (restrict-triangle π g bg f))
      in comp₌-cong (id₌ bf) (normalized ∙ first) ∙
        comp₌-assoc bf (restrict-triangle π g′ bg′ f) (π ◁ (α ▷ f))

    compatible-post : {X Y Z B : CAT Γ} (π : MAP Z B)
      (g : MAP Y Z) {q : MAP Y B} {f f′ : MAP X Y} {r : MAP X B}
      (bg : (π ∘ g) =₁ q)
      (bf : (q ∘ f) =₁ r) (bf′ : (q ∘ f′) =₁ r) (α : f =₁ f′)
      → CompatibleOver q bf bf′ α
      → CompatibleOver π (compose-triangle π g bg f bf)
          (compose-triangle π g bg f′ bf′) (g ◁ α)
    compatible-post π g {q} {f} {f′} bg bf bf′ α compatible =
      comp₌-cong compatible (id₌ (restrict-triangle π g bg f)) ∙
      ((comp₌-assoc bf′ (q ◁ α) (restrict-triangle π g bg f)) ⁻¹ ∙
      (comp₌-cong (id₌ bf′) (restrict-change-square-One π g q bg α) ∙
        comp₌-assoc bf′ (restrict-triangle π g bg f′) (π ◁ (g ◁ α))))

    compatible-assoc : {W X Y Z B : CAT Γ} (π : MAP Z B)
      (h : MAP Y Z) (g : MAP X Y) (f : MAP W X)
      {q : MAP Y B} {r : MAP X B} {s : MAP W B}
      (bh : (π ∘ h) =₁ q) (bg : (q ∘ g) =₁ r) (bf : (r ∘ f) =₁ s)
      → CompatibleOver π
          (compose-triangle π (h ∘ g) (compose-triangle π h bh g bg) f bf)
          (compose-triangle π h bh (g ∘ f) (compose-triangle q g bg f bf))
          (comp-assoc f g h)
    compatible-assoc π h g f {q} bh bg bf =
      let A = comp-assoc f g q
          D′ = comp-assoc f (h ∘ g) π
          t = restrict-triangle π h bh g ▷ f
          u = bg ▷ f
          v = restrict-triangle π h bh (g ∘ f)
          w = π ◁ comp-assoc f g h
          middle = comp₌-cong ((preWhisker-comp₌ bg (restrict-triangle π h bh g) f) ⁻¹)
              (id₌ (D′ ⁻¹)) ∙
            ((comp₌-assoc u t (D′ ⁻¹)) ⁻¹ ∙
            (comp₌-cong (id₌ u) (comp₌-cong (inv-comp-left A t) (id₌ (D′ ⁻¹))) ∙
              reassociateFour u (A ⁻¹) (A ∙ t) (D′ ⁻¹)))
      in comp₌-cong (id₌ bf)
          (middle ∙ comp₌-cong (id₌ (restrict-triangle q g bg f))
            ((restrict-triangle-twice π h bh g f) ⁻¹)) ∙
        (comp₌-assoc bf (restrict-triangle q g bg f) (v ∙ w) ∙
          comp₌-assoc (bf ∙ restrict-triangle q g bg f) v w)

    compatible-unitˡ : {X Y B : CAT Γ} (π : MAP Y B) (f : MAP X Y) {q : MAP X B}
      (bf : (π ∘ f) =₁ q)
      → CompatibleOver π (compose-triangle π (id Y) (comp-unitʳ π) f bf) bf (comp-unitˡ f)
    compatible-unitˡ π f bf =
      let A = comp-assoc f (id _) π
      in comp₌-cong (id₌ bf)
        ((comp-inv-right (π ◁ comp-unitˡ f) A ∙
          comp₌-cong (triangle-whiskered f π) (id₌ (A ⁻¹))) ⁻¹)

    compatible-unitʳ : {X Y B : CAT Γ} (π : MAP Y B) (f : MAP X Y) {q : MAP X B}
      (bf : (π ∘ f) =₁ q)
      → CompatibleOver π (compose-triangle π f bf (id X) (comp-unitʳ q)) bf (comp-unitʳ f)
    compatible-unitʳ π f {q} bf = (restrict-triangle-id π f q bf) ⁻¹

    compatible-quotient : {X Y B : CAT Γ} (π : MAP Y B)
      {a b z : MAP X Y} {q : MAP X B}
      (at-a : (π ∘ a) =₁ q) (at-b : (π ∘ b) =₁ q) (at-z : (π ∘ z) =₁ q)
      (left : a =₁ z) (right : b =₁ z)
      → CompatibleOver π at-a at-z left → CompatibleOver π at-b at-z right
      → CompatibleOver π at-a at-b (right ⁻¹ ∙ left)
    compatible-quotient π at-a at-b at-z left right left-square right-square =
      compatible-comp π at-a at-z at-b (right ⁻¹) left
        (compatible-inverse π at-b at-z right right-square) left-square
```

## Changing the base

Postcomposing the base with `σ` postcomposes the triangles, and preserves
identifications over the base. Postcomposition of triangles is compatible
with composition of triangles, by the whiskered pentagon.

```agda
  abstract
    compatible-postcompose : {X Y B B′ : CAT Γ} (σ : MAP B B′) (π : MAP Y B)
      {f g : MAP X Y} {q : MAP X B}
      (bf : (π ∘ f) =₁ q) (bg : (π ∘ g) =₁ q) (α : f =₁ g)
      → CompatibleOver π bf bg α
      → CompatibleOver (σ ∘ π) (post-triangle σ π f bf) (post-triangle σ π g bg) α
    compatible-postcompose σ π {f} {g} bf bg α compatible =
      comp₌-cong
        ((postWhisker σ ◁ compatible) ∙ (postWhisker-comp₌ σ bg (π ◁ α)) ⁻¹)
        (id₌ (comp-assoc f π σ)) ∙
      ((comp₌-assoc (σ ◁ bg) (σ ◁ (π ◁ α)) (comp-assoc f π σ)) ⁻¹ ∙
      (comp₌-cong (id₌ (σ ◁ bg)) (postWhisker-comp-One α π σ) ∙
        comp₌-assoc (σ ◁ bg) (comp-assoc g π σ) ((σ ∘ π) ◁ α)))

    postcompose-compose : {X Y Z B B′ : CAT Γ} (σ : MAP B B′) (π : MAP Z B)
      (g : MAP Y Z) (f : MAP X Y) {q : MAP Y B} {r : MAP X B}
      (bg : (π ∘ g) =₁ q) (bf : (q ∘ f) =₁ r)
      → compose-triangle (σ ∘ π) g (post-triangle σ π g bg) f (post-triangle σ q f bf) =₂
          post-triangle σ π (g ∘ f) (compose-triangle π g bg f bf)
    postcompose-compose σ π g f {q} bg bf =
      let u = σ ◁ bf
          a = comp-assoc f q σ
          v = (σ ◁ bg) ▷ f
          b = comp-assoc g π σ ▷ f
          c = (comp-assoc f g (σ ∘ π)) ⁻¹
          d = σ ◁ (bg ▷ f)
          e = comp-assoc f (π ∘ g) σ
          t = σ ◁ (comp-assoc f g π) ⁻¹
          k = comp-assoc (g ∘ f) π σ
          p = σ ◁ comp-assoc f g π
          pentagon : (e ∙ (b ∙ c)) =₂ (t ∙ k)
          pentagon = comp₌-cong ((postWhisker-inverse σ (comp-assoc f g π)) ⁻¹) (id₌ k) ∙
            ((inverse-square₌ {t = e ∙ b} {b = k} {l = comp-assoc f g (σ ∘ π)} {r = p}
              ((pentagon-whiskered-right f g π σ) ⁻¹)) ⁻¹ ∙
              (comp₌-assoc e b c) ⁻¹)
          middle : (a ∙ ((v ∙ b) ∙ c)) =₂ (d ∙ (t ∙ k))
          middle = comp₌-cong (id₌ d) pentagon ∙
            (comp₌-assoc d e (b ∙ c) ∙
            (comp₌-cong (whisker-mixed-One bg f σ) (id₌ (b ∙ c)) ∙
            ((comp₌-assoc a v (b ∙ c)) ⁻¹ ∙
              comp₌-cong (id₌ a) (comp₌-assoc v b c))))
          merge : (u ∙ (d ∙ t)) =₂ (σ ◁ compose-triangle π g bg f bf)
          merge = (postWhisker-comp₌ σ bf (restrict-triangle π g bg f)) ⁻¹ ∙
            comp₌-cong (id₌ u)
              ((postWhisker-comp₌ σ (bg ▷ f) ((comp-assoc f g π) ⁻¹)) ⁻¹)
      in comp₌-cong merge (id₌ k) ∙
        ((comp₌-assoc u (d ∙ t) k) ⁻¹ ∙
        (comp₌-cong (id₌ u) ((comp₌-assoc d t k) ⁻¹) ∙
        (comp₌-cong (id₌ u) middle ∙
        (comp₌-cong (id₌ u)
          (comp₌-cong (id₌ a)
            (comp₌-cong (preWhisker-comp₌ (σ ◁ bg) (comp-assoc g π σ) f) (id₌ c))) ∙
          comp₌-assoc u a ((post-triangle σ π g bg ▷ f) ∙ c)))))
```

## Identifications between functors over a base

```agda
module _ {Γ : Context} {S : CAT Γ} where
  open CategoryOverBase
  open FunctorOverBase

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    IsIdentificationOver : {X Y : CategoryOverBase S}
      (F G : FunctorOverBase X Y) → ((functor F) ＝ (functor G)) → Set m
    IsIdentificationOver {X = X} {Y} F G α =
      SquareCell₌ (map Y ◁ α) (const (id₌ (map X))) (const (cell F)) (const (cell G))

  compatible-to-over : {X Y : CategoryOverBase S} {F G : FunctorOverBase X Y}
    {α : functor F =₁ functor G}
    → CompatibleOver (map Y) (cell F) (cell G) α → IsIdentificationOver F G α
  compatible-to-over {F = F} c = const-sides₌ ((comp₌-unitˡ (cell F)) ⁻¹ ∙ c)

  over-to-compatible : {X Y : CategoryOverBase S} {F G : FunctorOverBase X Y}
    {α : functor F =₁ functor G}
    → IsIdentificationOver F G α → CompatibleOver (map Y) (cell F) (cell G) α
  over-to-compatible {F = F} given = comp₌-unitˡ (cell F) ∙ unconst-sides₌ given

  identification-over-id : {A : CAT Γ} {X Y : CategoryOverBase S} (F : FunctorOverBase X Y)
    → IsIdentificationOver F F (const {P = A} (id₌ (functor F)))
  identification-over-id {Y = Y} F = lies-over-id (map Y) (cell F)

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    identification-over-comp : {X Y : CategoryOverBase S}
      {F G H : FunctorOverBase X Y}
      {β : ((functor G) ＝ (functor H))} {α : ((functor F) ＝ (functor G))}
      → IsIdentificationOver G H β → IsIdentificationOver F G α
      → IsIdentificationOver F H (β ∙ α)
    identification-over-comp {X = X} {Y} second first =
      replace-edges₌ (id₌ _) (comp₌-unitˡ (const (id₌ (map X))))
        (lies-over-comp (map Y) first second)

    identification-over-inverse : {X Y : CategoryOverBase S}
      {F G : FunctorOverBase X Y} {α : ((functor F) ＝ (functor G))}
      → IsIdentificationOver F G α → IsIdentificationOver G F (α ⁻¹)
    identification-over-inverse  {X} {Y} given =
      replace-edges₌ (id₌ _)
        (const-cong {X = A} (inverse-identity (map X)) ∙ (const-inv {X = A} (id₌ (map X))) ⁻¹)
        (lies-over-inverse (map Y) given)

    identification-over-post : {X Y Z : CategoryOverBase S}
      (H : FunctorOverBase Y Z) {F G : FunctorOverBase X Y}
      {α : ((functor F) ＝ (functor G))}
      → IsIdentificationOver F G α
      → IsIdentificationOver (comp-over H F) (comp-over H G) (functor H ◁ α)
    identification-over-post  {Y = Y} {Z} H {F} {G} {α} given =
      replace-sides₌
        (const-comp {X = A} (cell F) (restrict-triangle (map Z) (functor H) (cell H) (functor F)))
        (const-comp {X = A} (cell G) (restrict-triangle (map Z) (functor H) (cell H) (functor G)))
        (paste-square₌ (restrict-change-square (map Z) (functor H) (map Y) (cell H) α) given)

    identification-over-pre : {W X Y : CategoryOverBase S}
      {F G : FunctorOverBase X Y} (K : FunctorOverBase W X)
      {α : ((functor F) ＝ (functor G))}
      → IsIdentificationOver F G α
      → IsIdentificationOver (comp-over F K) (comp-over G K) (α ▷ functor K)
    identification-over-pre  {X = X} {Y} {F} {G} K {α} given =
      let restricted = replace-edges₌ (id₌ _)
            (const-cong {X = A} (preWhisker-id₌ (map X) (functor K)) ∙
              pre-constant (id₌ (map X)) (functor K))
            (restrict-square (map Y) α (const (id₌ (map X))) (cell F) (cell G) (functor K) given)
      in replace-sides₌
        (const-comp {X = A} (cell K) (restrict-triangle (map Y) (functor F) (cell F) (functor K)))
        (const-comp {X = A} (cell K) (restrict-triangle (map Y) (functor G) (cell G) (functor K)))
        (paste-square₌ restricted
          (transpose-square₌ (identity-square₌ (const {P = A} (cell K)))))

  identification-over-assoc : {V W X Y : CategoryOverBase S}
    (H : FunctorOverBase X Y) (G : FunctorOverBase W X) (F : FunctorOverBase V W)
    → IsIdentificationOver (comp-over (comp-over H G) F) (comp-over H (comp-over G F))
        (comp-assoc (functor F) (functor G) (functor H))
  identification-over-assoc {Y = Y} H G F = compatible-to-over
    (compatible-assoc (map Y) (functor H) (functor G) (functor F) (cell H) (cell G) (cell F))

  identification-over-unitˡ : {X Y : CategoryOverBase S} (F : FunctorOverBase X Y)
    → IsIdentificationOver (comp-over (id-over Y) F) F (comp-unitˡ (functor F))
  identification-over-unitˡ {Y = Y} F =
    compatible-to-over (compatible-unitˡ (map Y) (functor F) (cell F))

  identification-over-unitʳ : {X Y : CategoryOverBase S} (F : FunctorOverBase X Y)
    → IsIdentificationOver (comp-over F (id-over X)) F (comp-unitʳ (functor F))
  identification-over-unitʳ {Y = Y} F =
    compatible-to-over (compatible-unitʳ (map Y) (functor F) (cell F))
```

Two squares of functors over the base paste to a square over the base. The
pasted cell is that of `comp-square` in Squares: an associator, the
whiskered right square, an associator, the whiskered left square and an
associator, each an identification over the base.

```agda
  abstract
    identification-over-paste : {X₀ X₁ X₂ Y₀ Y₁ Y₂ : CategoryOverBase S}
      (x₀ : FunctorOverBase X₀ Y₀) (x₁ : FunctorOverBase X₁ Y₁) (x₂ : FunctorOverBase X₂ Y₂)
      (f : FunctorOverBase X₀ X₁) (g : FunctorOverBase X₁ X₂)
      (F : FunctorOverBase Y₀ Y₁) (G : FunctorOverBase Y₁ Y₂)
      {α : (functor x₁ ∘ functor f) =₁ (functor F ∘ functor x₀)}
      {β : (functor x₂ ∘ functor g) =₁ (functor G ∘ functor x₁)}
      → IsIdentificationOver (comp-over x₁ f) (comp-over F x₀) α
      → IsIdentificationOver (comp-over x₂ g) (comp-over G x₁) β
      → IsIdentificationOver (comp-over x₂ (comp-over g f)) (comp-over (comp-over G F) x₀)
          (Square.cell (comp-square (square (functor g) (functor G) β)
            (square (functor f) (functor F) α)))
    identification-over-paste x₀ x₁ x₂ f g F G left right =
      identification-over-comp (identification-over-inverse (identification-over-assoc G F x₀))
        (identification-over-comp (identification-over-post G left)
          (identification-over-comp (identification-over-assoc G x₁ f)
            (identification-over-comp (identification-over-pre f right)
              (identification-over-inverse (identification-over-assoc x₂ g f)))))
```

An identification over the base, packaged with its compatibility.

```agda
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    record IdentificationOver {X Y : CategoryOverBase S} (F G : FunctorOverBase X Y) : Set m where
      constructor identification-over
      field
        identification : functor F ＝ functor G
        over : IsIdentificationOver F G identification

    id-identification-over : {X Y : CategoryOverBase S} (F : FunctorOverBase X Y)
      → IdentificationOver F F
    id-identification-over F = identification-over (const (id₌ (functor F)))
      (identification-over-id F)

    comp-identification-over : {X Y : CategoryOverBase S} {F G H : FunctorOverBase X Y}
      → IdentificationOver G H → IdentificationOver F G → IdentificationOver F H
    comp-identification-over β α = identification-over
      (IdentificationOver.identification β ∙ IdentificationOver.identification α)
      (identification-over-comp (IdentificationOver.over β) (IdentificationOver.over α))

    inverse-identification-over : {X Y : CategoryOverBase S} {F G : FunctorOverBase X Y}
      → IdentificationOver F G → IdentificationOver G F
    inverse-identification-over α = identification-over
      ((IdentificationOver.identification α) ⁻¹)
      (identification-over-inverse (IdentificationOver.over α))
```

Changing the base along `k : S → T` postcomposes the cells, and preserves
identifications over the base.

```agda
module _ {Γ : Context} {S : CAT Γ} where
  open CategoryOverBase
  open FunctorOverBase

  postcompose-over : {T : CAT Γ} (k : MAP S T) {X Y : CategoryOverBase S}
    → FunctorOverBase X Y → FunctorOverBase (postcompose-base k X) (postcompose-base k Y)
  postcompose-over k {Y = Y} F =
    functor-over (functor F) (post-triangle k (map Y) (functor F) (cell F))

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    identification-over-postcompose : {T : CAT Γ} (k : MAP S T) {X Y : CategoryOverBase S}
      {F G : FunctorOverBase X Y} {α : ((functor F) ＝ (functor G))}
      → IsIdentificationOver F G α
      → IsIdentificationOver (postcompose-over k F) (postcompose-over k G) α
    identification-over-postcompose  k {X} {Y} {F} {G} {α} given =
      replace-edges₌ (id₌ _)
        (const-cong {X = A} (postWhisker-id₌ k (map X)) ∙ post-constant k (id₌ (map X)))
        (post-triangle-inner k (map Y) α (const (id₌ (map X))) (cell F) (cell G) given)
```

## Restricting a composite triangle

Restricting a composite triangle along `f` agrees with restricting its two
factors successively.

```agda
module _ {Γ : Context} where
  abstract
    restrict-composite-triangle : {X Y Z K E : CAT Γ} (π : MAP K E)
      (f : MAP X Y) (g : MAP Y Z) (h : MAP Z K)
      {ρ : MAP Z E} {u : MAP Y E}
      (q : (π ∘ h) =₁ ρ) (b : (ρ ∘ g) =₁ u)
      → ((restrict-triangle ρ g b f ∙ restrict-triangle π h q (g ∘ f)) ∙
            (π ◁ comp-assoc f g h)) =₂
          restrict-triangle π (h ∘ g) (b ∙ restrict-triangle π h q g) f
    restrict-composite-triangle π f g h {ρ} q b =
      let A = comp-assoc f g ρ
          B = comp-assoc f (h ∘ g) π
          t = restrict-triangle π h q g
          n = restrict-triangle π (h ∘ g) t f
          left = restrict-triangle ρ g b f
          right = restrict-triangle π h q (g ∘ f)
          image = π ◁ comp-assoc f g h
          expand = comp₌-assoc (b ▷ f) (t ▷ f) (B ⁻¹) ∙
            comp₌-cong (preWhisker-comp₌ b t f) (id₌ (B ⁻¹))
      in expand ⁻¹ ∙
        (comp₌-cong (id₌ (b ▷ f)) (inv-comp-left A n) ∙
          (comp₌-assoc (b ▷ f) (A ⁻¹) (A ∙ n) ∙
            (comp₌-cong (id₌ left) (restrict-triangle-assoc π h q g f) ∙
              comp₌-assoc left right image)))
```

## Projecting a pasted square

A pasted square of functors, projected along `π` with triangles along the
two outer columns, lies over the corresponding pasting of the projected
squares.

```agda
  module ProjectedPasting {A₀ A₁ A₂ B₀ B₁ B₂ E : CAT Γ}
    (f : MAP A₀ A₁) (g : MAP A₁ A₂) (F : MAP B₀ B₁) (G : MAP B₁ B₂)
    (s₀ : MAP A₀ B₀) (s₁ : MAP A₁ B₁) (s₂ : MAP A₂ B₂)
    (π : MAP B₂ E) (ρ : MAP A₂ E) (u : MAP B₁ E) (v : MAP A₁ E)
    (q : (π ∘ s₂) =₁ ρ) (b : (π ∘ G) =₁ u) (B : (ρ ∘ g) =₁ v)
    (β : (s₂ ∘ g) =₁ (G ∘ s₁)) (α : (s₁ ∘ f) =₁ (F ∘ s₀))
    (ν : v =₁ (u ∘ s₁)) where

    pasted : (s₂ ∘ (g ∘ f)) =₁ ((G ∘ F) ∘ s₀)
    pasted = Square.cell (comp-square (square g G β) (square f F α))

    source-projection : (π ∘ (s₂ ∘ (g ∘ f))) =₁ (v ∘ f)
    source-projection = restrict-triangle ρ g B f ∙ restrict-triangle π s₂ q (g ∘ f)
    first-projection : (π ∘ ((s₂ ∘ g) ∘ f)) =₁ (v ∘ f)
    first-projection = restrict-triangle π (s₂ ∘ g) (B ∙ restrict-triangle π s₂ q g) f
    second-projection : (π ∘ ((G ∘ s₁) ∘ f)) =₁ ((u ∘ s₁) ∘ f)
    second-projection = restrict-triangle π (G ∘ s₁) (restrict-triangle π G b s₁) f
    third-projection : (π ∘ (G ∘ (s₁ ∘ f))) =₁ (u ∘ (s₁ ∘ f))
    third-projection = restrict-triangle π G b (s₁ ∘ f)
    fourth-projection : (π ∘ (G ∘ (F ∘ s₀))) =₁ (u ∘ (F ∘ s₀))
    fourth-projection = restrict-triangle π G b (F ∘ s₀)
    target-projection : (π ∘ ((G ∘ F) ∘ s₀)) =₁ ((u ∘ F) ∘ s₀)
    target-projection = restrict-triangle π (G ∘ F) (restrict-triangle π G b F) s₀

    projected-action : (v ∘ f) =₁ ((u ∘ F) ∘ s₀)
    projected-action = (comp-assoc s₀ F u) ⁻¹ ∙
      ((u ◁ α) ∙ (comp-assoc f s₁ u ∙ (ν ▷ f)))

    abstract
      project-paste :
        SquareCell₌ (π ◁ β) ν (B ∙ restrict-triangle π s₂ q g) (restrict-triangle π G b s₁)
        → SquareCell₌ (π ◁ pasted) projected-action source-projection target-projection
      project-paste given =
        let first = (comp₌-unitˡ-One source-projection) ⁻¹ ∙
              compatible-inverse π first-projection source-projection (comp-assoc f g s₂)
                (restrict-composite-triangle π f g s₂ q B)
            second = restrict-square-One π β ν
              (B ∙ restrict-triangle π s₂ q g) (restrict-triangle π G b s₁) f given
            third = restrict-triangle-assoc π G b s₁ f
            fourth = restrict-change-square-One π G u b α
            fifth = lies-over-inverse π (restrict-triangle-assoc π G b F s₀)
            firstTwo = replace-edges₌ (id₌ _) (comp₌-unitʳ-One (ν ▷ f))
              (lies-over-comp π first second)
        in lies-over-comp π
          (lies-over-comp π (lies-over-comp π firstTwo third) fourth) fifth
```
