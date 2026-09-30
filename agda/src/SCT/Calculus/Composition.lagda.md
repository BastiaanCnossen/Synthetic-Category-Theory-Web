# Composition and cancellation

We separate composition from its laws. The comparison type retains the
specified witnesses: it is not Agda equality, and no uniqueness of comparison
proofs is assumed. These records are interfaces for calculations, not a new
definition of synthetic category.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.Calculus.Composition where

open import Agda.Primitive using (Level; lsuc; _⊔_)

record Composition (o h p : Level) : Set (lsuc (o ⊔ h ⊔ p)) where
  infixr 30 _∘_
  infix 10 _≈_
  field
    Obj : Set o
    Hom : Obj → Obj → Set h
    _≈_ : {x y : Obj} → Hom x y → Hom x y → Set p
    id : (x : Obj) → Hom x x
    _∘_ : {x y z : Obj} → Hom y z → Hom x y → Hom x z
    refl : {x y : Obj} (f : Hom x y) → f ≈ f
    sym : {x y : Obj} {f g : Hom x y} → f ≈ g → g ≈ f
    trans : {x y : Obj} {f g h : Hom x y} → g ≈ h → f ≈ g → f ≈ h
    congr : {x y z : Obj} {g g′ : Hom y z} {f f′ : Hom x y}
      → g ≈ g′ → f ≈ f′ → (g ∘ f) ≈ (g′ ∘ f′)

record Laws {o h p : Level} (C : Composition o h p) : Set (o ⊔ h ⊔ p) where
  open Composition C
  field
    assoc : {w x y z : Obj} (h : Hom y z) (g : Hom x y) (f : Hom w x)
      → ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
    unitˡ : {x y : Obj} (f : Hom x y) → (id y ∘ f) ≈ f
    unitʳ : {x y : Obj} (f : Hom x y) → (f ∘ id x) ≈ f
```

Cancellation needs only the displayed inverse comparison. It does not
require an inverse operation or a global choice of inverses. Reassociate,
apply that comparison, and remove the identity.

```agda
module Calculation {o h p : Level} (C : Composition o h p) (L : Laws C) where
  open Composition C
  open Laws L

  abstract
    cancel-left : {x y z : Obj} (r : Hom z y) (s : Hom y z) (f : Hom x y)
      → (r ∘ s) ≈ id y → (r ∘ (s ∘ f)) ≈ f
    cancel-left r s f inverse =
      trans (unitˡ f) (trans (congr inverse (refl f)) (sym (assoc r s f)))

    cancel-right : {x y z : Obj} (f : Hom y z) (s : Hom x y) (r : Hom y x)
      → (s ∘ r) ≈ id y → ((f ∘ s) ∘ r) ≈ f
    cancel-right f s r inverse =
      trans (unitʳ f) (trans (congr (refl f) inverse) (assoc f s r))

    reassociate-four : {v w x y z : Obj}
      (k : Hom y z) (h : Hom x y) (g : Hom w x) (f : Hom v w)
      → (((k ∘ h) ∘ g) ∘ f) ≈ (k ∘ (h ∘ (g ∘ f)))
    reassociate-four k h g f =
      trans (assoc k h (g ∘ f)) (assoc (k ∘ h) g f)
```
