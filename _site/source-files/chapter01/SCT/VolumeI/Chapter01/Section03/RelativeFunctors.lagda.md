# Categories and functors over a base

A category over `S` carries its structural functor to `S`. A functor over
the base carries a specified triangle, oriented as in the existing
factorization convention: target projection after the functor equals the
source projection. These records specify data; they do not postulate a
category of relative categories or any new coherence laws.

The file develops identity, composition and inversion over a base, change
of base by postcomposition, the square of a functor over a base map,
uniqueness and mutual functors over a base, equivalences over a base, and
the dual data under a base. Factorizations and extensions are views of
these records, in Factorizations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.RelativeFunctors where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open import SCT.VolumeI.Chapter01.Section03.Squares
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (ReflectsIdentifications; equiv-compose; equiv-inverse)
open Operations
open Composition

module _ {Γ : Context} where
  record CategoryOverBase (S : CAT Γ) : Set (c ⊔ m) where
    constructor category-over
    field
      category : CAT Γ
      map : MAP category S

  record FunctorOverBase {S : CAT Γ}
    (X Y : CategoryOverBase S) : Set m where
    constructor functor-over
    field
      functor : MAP (CategoryOverBase.category X) (CategoryOverBase.category Y)
      cell : (CategoryOverBase.map Y ∘ functor) =₁ CategoryOverBase.map X

  id-over : {S : CAT Γ} (X : CategoryOverBase S) → FunctorOverBase X X
  id-over X = functor-over (id (CategoryOverBase.category X))
    (comp-unitʳ (CategoryOverBase.map X))

  comp-over : {S : CAT Γ} {X Y Z : CategoryOverBase S}
    → FunctorOverBase Y Z → FunctorOverBase X Y → FunctorOverBase X Z
  comp-over {Z = Z} G F = functor-over (functor G ∘ functor F)
    (cell F ∙ ((cell G ▷ functor F) ∙
      (comp-assoc (functor F) (functor G) (CategoryOverBase.map Z)) ⁻¹))
    where open FunctorOverBase

  inverse-over : {S : CAT Γ} {X Y : CategoryOverBase S}
    (F : FunctorOverBase X Y) → IsEquiv (FunctorOverBase.functor F)
    → FunctorOverBase Y X
  inverse-over {Y = Y} F e = functor-over (IsEquiv.inverse e)
    (comp-unitʳ q ∙
      ((q ◁ (IsEquiv.right-inverse-law e) ⁻¹) ∙
        (comp-assoc (IsEquiv.inverse e) (FunctorOverBase.functor F) q ∙
          ((FunctorOverBase.cell F) ⁻¹ ▷ IsEquiv.inverse e))))
    where
      q = CategoryOverBase.map Y
```

## Changing the base by postcomposition

`postcompose-base` leaves the category unchanged. A functor over a map
`k : S → T` is an ordinary functor over `T` from this postcomposed object.
The order of objects is always source, then target. For an identity base
map, the structural projection contains `id ∘ p`; it is related to `p`
by the unitor, not by definitional equality.

```agda
  postcompose-base : {S T : CAT Γ} → MAP S T → CategoryOverBase S → CategoryOverBase T
  postcompose-base k X = category-over (CategoryOverBase.category X)
    (k ∘ CategoryOverBase.map X)

  FunctorOverMap : {S T : CAT Γ} (k : MAP S T)
    → CategoryOverBase S → CategoryOverBase T → Set m
  FunctorOverMap k X Y = FunctorOverBase (postcompose-base k X) Y

  comp-over-map : {S T : CAT Γ} (k : MAP S T)
    {X Y : CategoryOverBase S} {Z : CategoryOverBase T}
    → FunctorOverMap k Y Z → FunctorOverBase X Y → FunctorOverMap k X Z
  comp-over-map k {Y = Y} {Z} G F = functor-over (functor G ∘ functor F)
    ((k ◁ cell F) ∙
      (comp-assoc (functor F) (CategoryOverBase.map Y) k ∙
        ((cell G ▷ functor F) ∙
          (comp-assoc (functor F) (functor G) (CategoryOverBase.map Z)) ⁻¹)))
    where open FunctorOverBase
```

## A square over a map of bases

A functor over a map of bases already carries the required specified cell.
The adapter reorganizes the boundary as a square between the functor and
the base map, reversing that cell using the chosen inversion.

```agda
  over-map-square : {S T : CAT Γ} {k : MAP S T}
    {X : CategoryOverBase S} {Y : CategoryOverBase T}
    (F : FunctorOverMap k X Y)
    → Square (FunctorOverBase.functor F) k
  over-map-square {X = X} {Y} F = square
    (CategoryOverBase.map X) (CategoryOverBase.map Y)
    ((FunctorOverBase.cell F) ⁻¹)
```

## Uniqueness and mutual functors over a base

`ReflectsIdentifications` from Equivalences keeps its testing source
explicit. Two functors over the base are compared using reflection by the
target projection at the source category. The conclusion identifies the
underlying functors only; no compatibility with the two cells is claimed.
For functors over the base in both directions, reflection at both
categories identifies the two composites with identities, so either functor
is an equivalence with the other as chosen inverse.

```agda
  functor-over-unique : {S : CAT Γ} {X Y : CategoryOverBase S}
    → ReflectsIdentifications (CategoryOverBase.map Y) (CategoryOverBase.category X)
    → (F G : FunctorOverBase X Y)
    → FunctorOverBase.functor F =₁ FunctorOverBase.functor G
  functor-over-unique reflect F G = reflect _ _ ((cell G) ⁻¹ ∙ cell F)
    where open FunctorOverBase

  mutual-over-isEquiv : {S : CAT Γ} {X Y : CategoryOverBase S}
    → ReflectsIdentifications (CategoryOverBase.map X) (CategoryOverBase.category X)
    → ReflectsIdentifications (CategoryOverBase.map Y) (CategoryOverBase.category Y)
    → (F : FunctorOverBase X Y) (G : FunctorOverBase Y X)
    → IsEquiv (FunctorOverBase.functor F)
  mutual-over-isEquiv {X = X} {Y} reflect-X reflect-Y F G = record
    { inverse = FunctorOverBase.functor G
    ; left-inverse-law = (functor-over-unique reflect-X (comp-over G F) (id-over X)) ⁻¹
    ; right-inverse-law = (functor-over-unique reflect-Y (comp-over F G) (id-over Y)) ⁻¹ }
```

## Equivalences over a base

`EquivalenceOver X Y` is a functor over the base from `X` to `Y` whose
underlying functor is an equivalence. Objects are listed source first.
The specified cell is kept; inverse laws over the base are not
additional fields. Composition, inversion and composition along a map of
bases act on the functor over the base and on the equivalence separately.

```agda
  record EquivalenceOver {S : CAT Γ} (X Y : CategoryOverBase S) : Set m where
    constructor equivalence-over
    field
      functor-over-base : FunctorOverBase X Y
      isEquiv : IsEquiv (FunctorOverBase.functor functor-over-base)

  comp-equivalence-over : {S : CAT Γ} {X Y Z : CategoryOverBase S}
    → EquivalenceOver Y Z → EquivalenceOver X Y → EquivalenceOver X Z
  comp-equivalence-over G F = equivalence-over
    (comp-over (functor-over-base G) (functor-over-base F))
    (equiv-compose (FunctorOverBase.functor (functor-over-base F))
      (FunctorOverBase.functor (functor-over-base G)) (isEquiv F) (isEquiv G))
    where open EquivalenceOver

  inverse-equivalence-over : {S : CAT Γ} {X Y : CategoryOverBase S}
    → EquivalenceOver X Y → EquivalenceOver Y X
  inverse-equivalence-over F = equivalence-over
    (inverse-over (functor-over-base F) (isEquiv F)) (equiv-inverse (isEquiv F))
    where open EquivalenceOver
```

Composition along a map of bases uses the same calculation as
`comp-over-map`. The base map `k` need not be an equivalence; only the two
underlying functors are required to be equivalences.

```agda
  comp-equivalence-over-map : {S T : CAT Γ} (k : MAP S T)
    {X Y : CategoryOverBase S} {Z : CategoryOverBase T}
    → EquivalenceOver (postcompose-base k Y) Z → EquivalenceOver X Y
    → EquivalenceOver (postcompose-base k X) Z
  comp-equivalence-over-map k G F = equivalence-over
    (comp-over-map k (functor-over-base G) (functor-over-base F))
    (equiv-compose (FunctorOverBase.functor (functor-over-base F))
      (FunctorOverBase.functor (functor-over-base G)) (isEquiv F) (isEquiv G))
    where open EquivalenceOver
```

## Categories and functors under a base

The dual data carry a structural functor out of `S`. Here the cell has the
agreed orientation `Y.map = functor ∘ X.map`. Thus the old extension triangle
is recovered by inversion. No general duality mechanism is needed.

```agda
  record CategoryUnderBase (S : CAT Γ) : Set (c ⊔ m) where
    constructor category-under
    field
      category : CAT Γ
      map : MAP S category

  record FunctorUnderBase {S : CAT Γ}
    (X Y : CategoryUnderBase S) : Set m where
    constructor functor-under
    field
      functor : MAP (CategoryUnderBase.category X) (CategoryUnderBase.category Y)
      cell : CategoryUnderBase.map Y =₁ (functor ∘ CategoryUnderBase.map X)

  id-under : {S : CAT Γ} (X : CategoryUnderBase S) → FunctorUnderBase X X
  id-under X = functor-under (id (CategoryUnderBase.category X))
    ((comp-unitˡ (CategoryUnderBase.map X)) ⁻¹)

  comp-under : {S : CAT Γ} {X Y Z : CategoryUnderBase S}
    → FunctorUnderBase Y Z → FunctorUnderBase X Y → FunctorUnderBase X Z
  comp-under {X = X} G F = functor-under (functor G ∘ functor F)
    ((comp-assoc (CategoryUnderBase.map X) (functor F) (functor G)) ⁻¹ ∙
      ((functor G ◁ cell F) ∙ cell G))
    where open FunctorUnderBase
```

Uniqueness under the base uses reflection by precomposition with the
structural functor of the source, again at one explicit testing category:
`PrecompositionReflects l D` concerns functors from the target of `l` to
`D`. It identifies the underlying functors only. Mutual functors under the
base are then equivalences, as over the base.

```agda
  PrecompositionReflects : {C T : CAT Γ} → MAP C T → CAT Γ → Set m
  PrecompositionReflects {T = T} l D =
    (u v : MAP T D) → (u ∘ l) =₁ (v ∘ l) → u =₁ v

  functor-under-unique : {S : CAT Γ} {X Y : CategoryUnderBase S}
    → PrecompositionReflects (CategoryUnderBase.map X) (CategoryUnderBase.category Y)
    → (F G : FunctorUnderBase X Y)
    → FunctorUnderBase.functor F =₁ FunctorUnderBase.functor G
  functor-under-unique reflect F G = reflect _ _ (cell G ∙ (cell F) ⁻¹)
    where open FunctorUnderBase

  mutual-under-isEquiv : {S : CAT Γ} {X Y : CategoryUnderBase S}
    → PrecompositionReflects (CategoryUnderBase.map X) (CategoryUnderBase.category X)
    → PrecompositionReflects (CategoryUnderBase.map Y) (CategoryUnderBase.category Y)
    → (F : FunctorUnderBase X Y) (G : FunctorUnderBase Y X)
    → IsEquiv (FunctorUnderBase.functor F)
  mutual-under-isEquiv {X = X} {Y} reflect-X reflect-Y F G = record
    { inverse = FunctorUnderBase.functor G
    ; left-inverse-law = (functor-under-unique reflect-X (comp-under G F) (id-under X)) ⁻¹
    ; right-inverse-law = (functor-under-unique reflect-Y (comp-under F G) (id-under Y)) ⁻¹ }
```
