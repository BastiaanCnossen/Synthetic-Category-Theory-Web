# Squares for associators and unitors

The primitive structural-operation comparisons yield commuting squares with normalized functor-expression endpoints. These are the associator and unitor clauses of recursive identification comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ParameterizedWhiskering as Parameterized

module SCT.VolumeI.Chapter05.Section01.Expressions.StructuralSquares {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _⋆_; _◁_; _▷_; _⁻¹)
open Calculus.Local T

opaque
  assoc-natural : {B C D E : T.CAT}
    {f f' : T.MAP B C} {g g' : T.MAP C D} {h h' : T.MAP D E}
    (alpha : T._=₁_ f f') (beta : T._=₁_ g g') (gamma : T._=₁_ h h')
    → T._=₂_ (T.comp-assoc f' g' h' ∙ ((gamma ⋆ beta) ⋆ alpha))
      ((gamma ⋆ (beta ⋆ alpha)) ∙ T.comp-assoc f g h)
  assoc-natural {f = f} {f'} {g} {g'} {h} {h'} alpha beta gamma =
    isoComp-cong ((const-One (T.comp-assoc f' g' h')) ⁻¹) (T.idIso _) then
    Parameterized.horizontal-assoc T gamma beta alpha then
    isoComp-cong (T.idIso _) (const-One (T.comp-assoc f g h))

  unit-left-natural : {C D : T.CAT} {f g : T.MAP C D} (alpha : T._=₁_ f g)
    → T._=₂_ (T.comp-unitˡ g ∙ (T.idIso (T.id D) ⋆ alpha)) (alpha ∙ T.comp-unitˡ f)
  unit-left-natural {D = D} {f} {g} alpha =
    isoComp-cong ((const-One (T.comp-unitˡ g)) ⁻¹)
      (hcomp-cong ((const-One (T.idIso (T.id D))) ⁻¹) (T.idIso _)) then
    Parameterized.horizontal-unit-left T alpha then isoComp-cong (T.idIso _) (const-One (T.comp-unitˡ f))

  unit-right-natural : {C D : T.CAT} {f g : T.MAP C D} (alpha : T._=₁_ f g)
    → T._=₂_ (T.comp-unitʳ g ∙ (alpha ⋆ T.idIso (T.id C))) (alpha ∙ T.comp-unitʳ f)
  unit-right-natural {C = C} {f = f} {g} alpha =
    isoComp-cong ((const-One (T.comp-unitʳ g)) ⁻¹)
      (hcomp-cong (T.idIso _) ((const-One (T.idIso (T.id C))) ⁻¹)) then
    Parameterized.horizontal-unit-right T alpha then isoComp-cong (T.idIso _) (const-One (T.comp-unitʳ f))

  hcomp-left-factor : {B C D : T.CAT} {f f' : T.MAP B C} {g₀ g₁ g₂ : T.MAP C D}
    (q : T._=₁_ g₁ g₂) (p : T._=₁_ g₀ g₁) (a : T._=₁_ f f')
    → T._=₂_ ((q ∙ p) ⋆ a) ((q ⋆ a) ∙ (p ▷ f))
  hcomp-left-factor q p a = hcomp-cong (T.idIso _) ((isoComp-unitʳ-at a) ⁻¹) then
    hcomp-isoComp q p a (T.idIso _) then isoComp-cong (T.idIso _) (hcomp-idInner p _)

  hcomp-right-factor : {B C D : T.CAT} {f₀ f₁ f₂ : T.MAP B C} {g g' : T.MAP C D}
    (b : T._=₁_ g g') (q : T._=₁_ f₁ f₂) (p : T._=₁_ f₀ f₁)
    → T._=₂_ (b ⋆ (q ∙ p)) ((b ⋆ q) ∙ (g ◁ p))
  hcomp-right-factor b q p = hcomp-cong ((isoComp-unitʳ-at b) ⁻¹) (T.idIso _) then
    hcomp-isoComp b (T.idIso _) q p then isoComp-cong (T.idIso _) (hcomp-idOuter _ p)

module Associator {B C D E : S.CAT} (f : S.MAP B C) (g : S.MAP C D) (h : S.MAP D E)
  {f' : T.MAP (cat B) (cat C)} {g' : T.MAP (cat C) (cat D)} {h' : T.MAP (cat D) (cat E)}
  (alpha : T._=₁_ (map f) f') (beta : T._=₁_ (map g) g') (gamma : T._=₁_ (map h) h') where
  left = (((gamma ⋆ beta) ∙ comp g h) ⋆ alpha) ∙ comp f (S._∘_ h g)
  right = (gamma ⋆ ((beta ⋆ alpha) ∙ comp f g)) ∙ comp (S._∘_ g f) h
  basic-left = (comp g h ▷ map f) ∙ comp f (S._∘_ h g)
  basic-right = (map h ◁ comp f g) ∙ comp (S._∘_ g f) h
  opaque
    left-factor : T._=₂_ left (((gamma ⋆ beta) ⋆ alpha) ∙ basic-left)
    left-factor = isoComp-cong (hcomp-left-factor (gamma ⋆ beta) (comp g h) alpha) (T.idIso _) then
      isoComp-assoc-at ((gamma ⋆ beta) ⋆ alpha) (comp g h ▷ map f) (comp f (S._∘_ h g))
    right-factor : T._=₂_ right ((gamma ⋆ (beta ⋆ alpha)) ∙ basic-right)
    right-factor = isoComp-cong (hcomp-right-factor gamma (beta ⋆ alpha) (comp f g)) (T.idIso _) then
      isoComp-assoc-at (gamma ⋆ (beta ⋆ alpha)) (map h ◁ comp f g) (comp (S._∘_ g f) h)
    square : T._=₂_ (right ∙ term (S.comp-assoc f g h)) (T.comp-assoc f' g' h' ∙ left)
    square = isoComp-cong right-factor (T.idIso _) then
      isoComp-assoc-at (gamma ⋆ (beta ⋆ alpha)) basic-right (term (S.comp-assoc f g h)) then
      isoComp-cong (T.idIso _) (isoComp-assoc-at (map h ◁ comp f g) (comp (S._∘_ g f) h)
        (term (S.comp-assoc f g h)) then OperationCompatibility.associator K f g h) then
      (isoComp-assoc-at (gamma ⋆ (beta ⋆ alpha)) (T.comp-assoc (map f) (map g) (map h)) basic-left) ⁻¹ then
      isoComp-cong ((assoc-natural alpha beta gamma) ⁻¹) (T.idIso _) then
      isoComp-assoc-at (T.comp-assoc f' g' h') ((gamma ⋆ beta) ⋆ alpha) basic-left then
      isoComp-cong (T.idIso _) (left-factor ⁻¹)

opaque
  left-unit : {C D : S.CAT} (f : S.MAP C D) {f' : T.MAP (cat C) (cat D)}
    (alpha : T._=₁_ (map f) f')
    → T._=₂_ (alpha ∙ term (S.comp-unitˡ f))
      (T.comp-unitˡ f' ∙ ((unit D ⋆ alpha) ∙ comp f (S.id D)))
  left-unit {D = D} f {f'} alpha =
    isoComp-cong (T.idIso _) (OperationCompatibility.leftUnit K f) then
    (isoComp-assoc-at alpha (T.comp-unitˡ (map f)) ((unit D ▷ map f) ∙ comp f (S.id D))) ⁻¹ then
    isoComp-cong ((unit-left-natural alpha) ⁻¹) (T.idIso _) then
    reassociateFour (T.comp-unitˡ f') (T.idIso (T.id (cat D)) ⋆ alpha) (unit D ▷ map f) (comp f (S.id D)) then
    isoComp-cong (T.idIso _) (isoComp-cong
      (isoComp-cong (hcomp-idOuter (T.id (cat D)) alpha) (T.idIso _) then (interchange-at (unit D) alpha) ⁻¹)
      (T.idIso _))

  right-unit : {C D : S.CAT} (f : S.MAP C D) {f' : T.MAP (cat C) (cat D)}
    (alpha : T._=₁_ (map f) f')
    → T._=₂_ (alpha ∙ term (S.comp-unitʳ f))
      (T.comp-unitʳ f' ∙ ((alpha ⋆ unit C) ∙ comp (S.id C) f))
  right-unit {C = C} f {f'} alpha =
    isoComp-cong (T.idIso _) (OperationCompatibility.rightUnit K f) then
    (isoComp-assoc-at alpha (T.comp-unitʳ (map f)) ((map f ◁ unit C) ∙ comp (S.id C) f)) ⁻¹ then
    isoComp-cong ((unit-right-natural alpha) ⁻¹) (T.idIso _) then
    reassociateFour (T.comp-unitʳ f') (alpha ⋆ T.idIso (T.id (cat C))) (map f ◁ unit C) (comp (S.id C) f) then
    isoComp-cong (T.idIso _) (isoComp-cong (isoComp-cong (hcomp-idInner alpha (T.id (cat C))) (T.idIso _)) (T.idIso _))
```
