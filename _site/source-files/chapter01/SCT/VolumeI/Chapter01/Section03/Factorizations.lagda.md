# Factorizations and extensions

A factorization of `d : X → D` through `f : C → D` solves for a factor
functor `X → C` together with a specified triangle. It is a view of the
relative language: a functor over `D` from the category `X` with structural
functor `d` to the category `C` with structural functor `f`. Identity,
composition, inversion, uniqueness and mutual factorizations are therefore
the corresponding operations of RelativeFunctors, applied to these objects.
This file adds the constructions that are naturally phrased as solving for
a factor: changing the factored functor, restricting it, factoring through
an equivalence, and factorizations supplied by commuting squares.

Extensions are the dual view, using categories under a base. Their triangle
has the opposite orientation from the under-base cell.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Factorizations where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (ReflectsIdentifications)
open Operations
open Composition
```

## Factorizations as functors over a base

`factor` and `triangle` are the two components of the view. The triangle
is the cell of the functor over the base, with the same orientation as the
original factorization record: `f ∘ factor l =₁ d`.

```agda
module _ {Γ : Context} where
  module _ {C D X : CAT Γ} where
    open Terms.InContext X using (Term)

    Factorization : (f : MAP C D) (d : Term D) → Set m
    Factorization   f d = FunctorOverBase (category-over X d) (category-over C f)

    factor : {f : MAP C D} {d : Term D} → Factorization f d → Term C
    factor l = FunctorOverBase.functor l

    triangle : {f : MAP C D} {d : Term D}
      → (l : Factorization f d) → (f ∘ factor l) =₁ d
    triangle l = FunctorOverBase.cell l
```

## Changing and restricting the factored functor

An identification `d =₁ d′` changes the factored functor. Precomposition
with `p : Y → X` restricts a factorization of `d` to one of `d ∘ p`.

```agda
  module _ {C D X : CAT Γ} where
    open Terms.InContext X using (Term)

    factorization-retarget : {f : MAP C D} {d d′ : Term D}
      → d =₁ d′ → Factorization f d → Factorization f d′
    factorization-retarget α l = functor-over (factor l) (α ∙ triangle l)

    factorization-restrict : {Y : CAT Γ} {f : MAP C D} {d : Term D}
      → Factorization f d → (p : MAP Y X) → Factorization f (d ∘ p)
    factorization-restrict {f = f} l p = functor-over (factor l ∘ p)
      ((triangle l ▷ p) ∙ (comp-assoc p (factor l) f) ⁻¹)
```

## Factorizations from commuting squares

A commuting square `k ∘ m =₁ m′ ∘ k′` makes `k′` a factor of `k ∘ m`
through `m′`. Composing along `k`, a factorization of `d` through `m` then
gives a factorization of `k ∘ d` through `m′`. This is `comp-over-map` for
the square, viewed as a functor over `k`.

```agda
  square-factorization : {C C′ D E : CAT Γ} {k : MAP D E} {m : MAP C D}
    {m′ : MAP C′ E} {k′ : MAP C C′}
    → (k ∘ m) =₁ (m′ ∘ k′) → Factorization m′ (k ∘ m)
  square-factorization {k′ = k′} σ = functor-over k′ (σ ⁻¹)

  module _ {C C′ D E X : CAT Γ} where
    open Terms.InContext X using (Term)

    factorization-along-square : {k : MAP D E} {m : MAP C D}
      {m′ : MAP C′ E} {k′ : MAP C C′} {d : Term D}
      → (k ∘ m) =₁ (m′ ∘ k′) → Factorization m d → Factorization m′ (k ∘ d)
    factorization-along-square  {k = k} {m} σ F =
      comp-over-map k {Y = category-over C m} (square-factorization σ) F
```

## Factoring through an equivalence

The chosen inverse of an equivalence `f` gives a factorization of any `d`
through `f`. If `f ∘ u =₁ g ∘ v` with `u` an equivalence, then `f` factors
through `g` via `v` and the chosen inverse of `u`.

```agda
  module _ {C D X : CAT Γ} where
    open Terms.InContext X using (Term)

    factor-through-equiv : {f : MAP C D} (e : IsEquiv f)
      (d : Term D) → Factorization f d
    factor-through-equiv {f = f} e d = functor-over (IsEquiv.inverse e ∘ d)
      (comp-unitˡ d ∙
        (((IsEquiv.right-inverse-law e) ⁻¹ ▷ d) ∙ (comp-assoc d (IsEquiv.inverse e) f) ⁻¹))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    factorization-from-equivalent-source : {A B Z : CAT Γ}
      (f : MAP A Z) (g : MAP B Z) (u : MAP X A) (v : MAP X B)
      → IsEquiv u → (f ∘ u) =₁ (g ∘ v) → Factorization g f
    factorization-from-equivalent-source f g u v eu β = functor-over (v ∘ IsEquiv.inverse eu)
      (comp-unitʳ f ∙
        ((f ◁ (IsEquiv.right-inverse-law eu) ⁻¹) ∙
          (comp-assoc (IsEquiv.inverse eu) u f ∙
            ((β ⁻¹ ▷ IsEquiv.inverse eu) ∙ (comp-assoc (IsEquiv.inverse eu) v g) ⁻¹))))
```

## Recognizing an equivalence

If every functor into the target factors through `f`, and postcomposition
with `f` reflects identifications at every testing category, then `f` is
an equivalence. Factor the identity of the target to choose the inverse;
reflection at the source gives its other inverse law. This is the criterion
of `prop:equivalences_as_naive_bijections`, without a separate data record.

```agda
  factor-and-reflection-isEquiv : {C D : CAT Γ} (f : MAP C D)
    → ((T : CAT Γ) → ReflectsIdentifications f T)
    → ({T : CAT Γ} (d : MAP T D) → Factorization f d)
    → IsEquiv f
  factor-and-reflection-isEquiv {C} {D} f reflect factors = record
    { inverse = g
    ; left-inverse-law = (reflect C (g ∘ f) (id C) image) ⁻¹
    ; right-inverse-law = β ⁻¹ }
    where
    chosen : Factorization f (id D)
    chosen = factors (id D)
    g : MAP D C
    g = factor chosen
    β : (f ∘ g) =₁ id D
    β = triangle chosen
    image : (f ∘ (g ∘ f)) =₁ (f ∘ id C)
    image = (comp-unitʳ f) ⁻¹ ∙
      (comp-unitˡ f ∙ ((β ▷ f) ∙ (comp-assoc f g f) ⁻¹))
```

## Extensions

An extension of `d : C → D` along `l : C → T` is a functor `T → D` with a
specified identification of its restriction along `l` with `d`. It is a
functor under `C` from `T`, with structural functor `l`, to `D`, with
structural functor `d`. The under-base cell `d =₁ extension ∘ l` is the
inverse of the triangle of the original extension record; `extension-triangle`
recovers that orientation. Identity, composition, uniqueness and mutual
extensions are `id-under`, `comp-under`, `functor-under-unique` and
`mutual-under-isEquiv`. Changing the extended functor composes the cell with
the inverse of the given identification.

```agda
  Extension : {C D T : CAT Γ} (l : MAP C T) (d : MAP C D) → Set m
  Extension {D = D} {T} l d = FunctorUnderBase (category-under T l) (category-under D d)

  extension : {C D T : CAT Γ} {l : MAP C T} {d : MAP C D} → Extension l d → MAP T D
  extension E = FunctorUnderBase.functor E

  extension-triangle : {C D T : CAT Γ} {l : MAP C T} {d : MAP C D}
    → (E : Extension l d) → (extension E ∘ l) =₁ d
  extension-triangle E = (FunctorUnderBase.cell E) ⁻¹

  extension-retarget : {C D T : CAT Γ} {l : MAP C T} {d d′ : MAP C D}
    → d =₁ d′ → Extension l d → Extension l d′
  extension-retarget α E = functor-under (extension E) (FunctorUnderBase.cell E ∙ α ⁻¹)
```
