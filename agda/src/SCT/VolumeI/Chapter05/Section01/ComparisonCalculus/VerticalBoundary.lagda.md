# Boundaries of the vertical laws

The identity, inverse, and composition operations on identification animae determine the normalized boundaries of the vertical laws. These parameterized comparisons are used to type preservation of their selected witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyWitness as FamilyWitness

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.VerticalBoundary {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Operations W using (family; family-composite; family-const; vertical-family)

opaque
  identity-family : {C D : S.CAT} (f g : S.MAP C D)
    → T._=₁_ (family (S.id (S._＝_ f g))) (phi f g)
  identity-family f g = (phi f g ◁ unit (S._＝_ f g)) then T.comp-unitʳ (phi f g)

opaque
  identity-constant : {X C D : S.CAT} (f : S.MAP C D)
    → T._=₁_ (family (S.const {P = X} (S.idIso f))) (T.const (T.idIso (map f)))
  identity-constant f = family-const (S.idIso f) then const-cong (OperationCompatibility.identityIso K f)

opaque
  inverse-family : {X C D : S.CAT} {f g : S.MAP C D}
    (alpha : S.MAP X (S._＝_ f g))
    → T._=₁_ (family (S._⁻¹ alpha)) ((family alpha) ⁻¹)
  inverse-family {f = f} {g} alpha =
    family-composite S.＝-inv alpha then
    (OperationCompatibility.inversion K f g ▷ map alpha) then
    T.comp-assoc (map alpha) (phi f g) T.＝-inv

module Unary {C D : S.CAT} (f g : S.MAP C D) where
  private
    sigma = S.id (S._＝_ f g)
    q = phi f g
    s-id : T._=₁_ (family sigma) q
    s-id = identity-family f g
    s-inv : T._=₁_ (family (S._⁻¹ sigma)) (q ⁻¹)
    s-inv = inverse-family sigma then (T.＝-inv ◁ s-id)

  opaque
    left-boundary : T._=₁_ (family (S._∙_ (S.const (S.idIso g)) sigma))
      (T.const (T.idIso (map g)) ∙ q)
    left-boundary = vertical-family K (S.const (S.idIso g)) sigma then
      isoComp-cong (identity-constant g) s-id

  opaque
    right-boundary : T._=₁_ (family (S._∙_ sigma (S.const (S.idIso f))))
      (q ∙ T.const (T.idIso (map f)))
    right-boundary = vertical-family K sigma (S.const (S.idIso f)) then
      isoComp-cong s-id (identity-constant f)

  opaque
    inverse-left-boundary : T._=₁_ (family (S._∙_ (S._⁻¹ sigma) sigma)) ((q ⁻¹) ∙ q)
    inverse-left-boundary = vertical-family K (S._⁻¹ sigma) sigma then isoComp-cong s-inv s-id

  opaque
    inverse-right-boundary : T._=₁_ (family (S._∙_ sigma (S._⁻¹ sigma))) (q ∙ (q ⁻¹))
    inverse-right-boundary = vertical-family K sigma (S._⁻¹ sigma) then isoComp-cong s-id s-inv

  module Left = FamilyWitness W (S._∙_ (S.const (S.idIso g)) sigma) sigma (phi f g)
    (T.const (T.idIso (map g)) ∙ q) q left-boundary s-id
  module Right = FamilyWitness W (S._∙_ sigma (S.const (S.idIso f))) sigma (phi f g)
    (q ∙ T.const (T.idIso (map f))) q right-boundary s-id
  module InverseLeft = FamilyWitness W (S._∙_ (S._⁻¹ sigma) sigma) (S.const (S.idIso f)) (phi f f)
    ((q ⁻¹) ∙ q) (T.const (T.idIso (map f))) inverse-left-boundary (identity-constant f)
  module InverseRight = FamilyWitness W (S._∙_ sigma (S._⁻¹ sigma)) (S.const (S.idIso g)) (phi g g)
    (q ∙ (q ⁻¹)) (T.const (T.idIso (map g))) inverse-right-boundary (identity-constant g)

  -- Specializations of the actual target primitive witnesses at q.
  -- These are still identifications between functors on W(f = g).
  opaque
    target-inverse-left : T._=₁_ ((q ⁻¹) ∙ q) (T.const (T.idIso (map f)))
    target-inverse-left = specialize (T.isoComp-inverseˡ (map f) (map g)) q
      (isoComp-evaluate ((T.id _) ⁻¹) (T.id _) q
        (T.comp-assoc q (T.id _) T.＝-inv then (T.＝-inv ◁ T.comp-unitˡ q)) (T.comp-unitˡ q))
      (const-pre (T.idIso (map f)) q)

  opaque
    target-inverse-right : T._=₁_ (q ∙ (q ⁻¹)) (T.const (T.idIso (map g)))
    target-inverse-right = specialize (T.isoComp-inverseʳ (map f) (map g)) q
      (isoComp-evaluate (T.id _) ((T.id _) ⁻¹) q (T.comp-unitˡ q)
        (T.comp-assoc q (T.id _) T.＝-inv then (T.＝-inv ◁ T.comp-unitˡ q)))
      (const-pre (T.idIso (map g)) q)

module Associativity {C D : S.CAT} (f g h k : S.MAP C D) where
  X = S._×_ (S._＝_ h k) (S._×_ (S._＝_ g h) (S._＝_ f g))
  alpha : S.MAP X (S._＝_ f g)
  alpha = S._∘_ S.pr₂ S.pr₂
  beta : S.MAP X (S._＝_ g h)
  beta = S._∘_ S.pr₁ S.pr₂
  gamma : S.MAP X (S._＝_ h k)
  gamma = S.pr₁

  opaque
    left-boundary : T._=₁_ (family (S._∙_ (S._∙_ gamma beta) alpha))
      ((family gamma ∙ family beta) ∙ family alpha)
    left-boundary = vertical-family K (S._∙_ gamma beta) alpha then
      isoComp-cong (vertical-family K gamma beta) (T.idIso _)

  opaque
    right-boundary : T._=₁_ (family (S._∙_ gamma (S._∙_ beta alpha)))
      (family gamma ∙ (family beta ∙ family alpha))
    right-boundary = vertical-family K gamma (S._∙_ beta alpha) then
      isoComp-cong (T.idIso _) (vertical-family K beta alpha)

  module Law = FamilyWitness W (S._∙_ (S._∙_ gamma beta) alpha) (S._∙_ gamma (S._∙_ beta alpha))
    (phi f k) ((family gamma ∙ family beta) ∙ family alpha) (family gamma ∙ (family beta ∙ family alpha))
    left-boundary right-boundary

  opaque
    target : T._=₁_ ((family gamma ∙ family beta) ∙ family alpha)
      (family gamma ∙ (family beta ∙ family alpha))
    target = assoc (family gamma) (family beta) (family alpha)

-- This file derives boundaries, not preservation of the chosen law witnesses.
```
