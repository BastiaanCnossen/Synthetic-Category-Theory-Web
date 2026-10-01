# Boundaries of the horizontal laws

These formulas compare the two boundaries of each horizontal-composition law. They provide the types in which preservation of the selected witnesses can be stated.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyPasting as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.HorizontalTransport as Horizontal
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.VerticalBoundary as Vertical
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ParameterizedWhiskering as Parameterized
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyWitness as FamilyWitness

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.HorizontalBoundary {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _⋆_; _◁_; _▷_; _⁻¹)
open Calculus T
open Operations W using (family)
open Boundaries W using (conjugate)

opaque
  identity-square : {X C D : S.CAT} (f : S.MAP C D)
    {F : T.MAP (cat C) (cat D)} (p : T._=₁_ (map f) F)
    → T._=₁_ (T.const p ∙ family (S.const {P = X} (S.idIso f))) (T.const (T.idIso F) ∙ T.const p)
  identity-square f p = Pasting.constant W K p p (S.idIso f) (T.idIso _)
    (isoComp-cong (T.idIso _) (OperationCompatibility.identityIso K f) then
      isoComp-unitʳ-at p then (isoComp-unitˡ-at p) ⁻¹)

  variable-square : {C D : S.CAT} (f g : S.MAP C D)
    → T._=₁_ (T.const (T.idIso (map g)) ∙ family (S.id (S._＝_ f g)))
      (phi f g ∙ T.const (T.idIso (map f)))
  variable-square f g = unitˡ _ then Vertical.identity-family W K f g then (unitʳ (phi f g)) ⁻¹

module LeftUnit {C D : S.CAT} (f g : S.MAP C D) where
  sigma = S.id (S._＝_ f g)
  eps = S.const {P = S._＝_ f g} (S.idIso (S.id D))
  eps' = T.const {P = cat (S._＝_ f g)} (T.idIso (T.id (cat D)))
  r : (i : S.MAP C D) → T._=₁_ (map (S._∘_ (S.id D) i)) (T.id (cat D) ∘ map i)
  r i = (unit D ⋆ T.idIso (map i)) ∙ comp i (S.id D)
  a = S._∙_ (S.const (S.comp-unitˡ g)) (S._⋆_ eps sigma)
  b = S._∙_ sigma (S.const (S.comp-unitˡ f))
  a' = T.const (T.comp-unitˡ (map g)) ∙ (eps' ⋆ phi f g)
  b' = phi f g ∙ T.const (T.comp-unitˡ (map f))
  adjust = conjugate (r f) (T.idIso (map g))
  output = adjust ∘ phi (S._∘_ (S.id D) f) g

  opaque
    unit-square : (i : S.MAP C D)
      → T._=₂_ (T.idIso (map i) ∙ term (S.comp-unitˡ i)) (T.comp-unitˡ (map i) ∙ r i)
    unit-square i = isoComp-unitˡ-at _ then OperationCompatibility.leftUnit K i then
      isoComp-cong (T.idIso _) (isoComp-cong ((hcomp-idInner (unit D) (map i)) ⁻¹) (T.idIso _))
    left : T._=₁_ (output ∘ map a) a'
    left = T.comp-assoc (map a) (phi (S._∘_ (S.id D) f) g) adjust then
      Squares.solve T (r f) (T.idIso (map g)) (family a) a'
        (Pasting.vertical W K (r f) (r g) (T.idIso (map g))
          (S._⋆_ eps sigma) (S.const (S.comp-unitˡ g)) (eps' ⋆ phi f g) (T.const (T.comp-unitˡ (map g)))
          (Horizontal.horizontal-square W K (T.idIso (map f)) (T.idIso (map g)) (unit D) (unit D)
            sigma (phi f g) eps eps' (variable-square f g) (identity-square (S.id D) (unit D)))
          (Pasting.constant W K (r g) (T.idIso (map g)) (S.comp-unitˡ g) (T.comp-unitˡ (map g)) (unit-square g)))
    right : T._=₁_ (output ∘ map b) b'
    right = T.comp-assoc (map b) (phi (S._∘_ (S.id D) f) g) adjust then
      Squares.solve T (r f) (T.idIso (map g)) (family b) b'
        (Pasting.vertical W K (r f) (T.idIso (map f)) (T.idIso (map g))
          (S.const (S.comp-unitˡ f)) sigma (T.const (T.comp-unitˡ (map f))) (phi f g)
          (Pasting.constant W K (r f) (T.idIso (map f)) (S.comp-unitˡ f) (T.comp-unitˡ (map f)) (unit-square f))
          (variable-square f g))
    target : T._=₁_ a' b'
    target = Parameterized.horizontal-unit-left T (phi f g)
  module Law = FamilyWitness W a b output a' b' left right

module RightUnit {C D : S.CAT} (f g : S.MAP C D) where
  sigma = S.id (S._＝_ f g)
  eps = S.const {P = S._＝_ f g} (S.idIso (S.id C))
  eps' = T.const {P = cat (S._＝_ f g)} (T.idIso (T.id (cat C)))
  r : (i : S.MAP C D) → T._=₁_ (map (S._∘_ i (S.id C))) (map i ∘ T.id (cat C))
  r i = (T.idIso (map i) ⋆ unit C) ∙ comp (S.id C) i
  a = S._∙_ (S.const (S.comp-unitʳ g)) (S._⋆_ sigma eps)
  b = S._∙_ sigma (S.const (S.comp-unitʳ f))
  a' = T.const (T.comp-unitʳ (map g)) ∙ (phi f g ⋆ eps')
  b' = phi f g ∙ T.const (T.comp-unitʳ (map f))
  adjust = conjugate (r f) (T.idIso (map g))
  output = adjust ∘ phi (S._∘_ f (S.id C)) g

  opaque
    unit-square : (i : S.MAP C D)
      → T._=₂_ (T.idIso (map i) ∙ term (S.comp-unitʳ i)) (T.comp-unitʳ (map i) ∙ r i)
    unit-square i = isoComp-unitˡ-at _ then OperationCompatibility.rightUnit K i then
      isoComp-cong (T.idIso _) (isoComp-cong ((hcomp-idOuter (map i) (unit C)) ⁻¹) (T.idIso _))
    left : T._=₁_ (output ∘ map a) a'
    left = T.comp-assoc (map a) (phi (S._∘_ f (S.id C)) g) adjust then
      Squares.solve T (r f) (T.idIso (map g)) (family a) a'
        (Pasting.vertical W K (r f) (r g) (T.idIso (map g))
          (S._⋆_ sigma eps) (S.const (S.comp-unitʳ g)) (phi f g ⋆ eps') (T.const (T.comp-unitʳ (map g)))
          (Horizontal.horizontal-square W K (unit C) (unit C) (T.idIso (map f)) (T.idIso (map g))
            eps eps' sigma (phi f g) (identity-square (S.id C) (unit C)) (variable-square f g))
          (Pasting.constant W K (r g) (T.idIso (map g)) (S.comp-unitʳ g) (T.comp-unitʳ (map g)) (unit-square g)))
    right : T._=₁_ (output ∘ map b) b'
    right = T.comp-assoc (map b) (phi (S._∘_ f (S.id C)) g) adjust then
      Squares.solve T (r f) (T.idIso (map g)) (family b) b'
        (Pasting.vertical W K (r f) (T.idIso (map f)) (T.idIso (map g))
          (S.const (S.comp-unitʳ f)) sigma (T.const (T.comp-unitʳ (map f))) (phi f g)
          (Pasting.constant W K (r f) (T.idIso (map f)) (S.comp-unitʳ f) (T.comp-unitʳ (map f)) (unit-square f))
          (variable-square f g))
    target : T._=₁_ a' b'
    target = Parameterized.horizontal-unit-right T (phi f g)
  module Law = FamilyWitness W a b output a' b' left right

module Associativity {B C D E : S.CAT} (f f' : S.MAP B C) (g g' : S.MAP C D) (h h' : S.MAP D E) where
  X = S._×_ (S._×_ (S._＝_ h h') (S._＝_ g g')) (S._＝_ f f')
  alpha : S.MAP X (S._＝_ f f')
  alpha = S.pr₂
  beta : S.MAP X (S._＝_ g g')
  beta = S._∘_ S.pr₂ S.pr₁
  gamma : S.MAP X (S._＝_ h h')
  gamma = S._∘_ S.pr₁ S.pr₁
  L : (i : S.MAP B C) (j : S.MAP C D) (k : S.MAP D E)
    → T._=₁_ (map (S._∘_ (S._∘_ k j) i)) ((map k ∘ map j) ∘ map i)
  L i j k = (comp j k ⋆ T.idIso (map i)) ∙ comp i (S._∘_ k j)
  R : (i : S.MAP B C) (j : S.MAP C D) (k : S.MAP D E)
    → T._=₁_ (map (S._∘_ k (S._∘_ j i))) (map k ∘ (map j ∘ map i))
  R i j k = (T.idIso (map k) ⋆ comp i j) ∙ comp (S._∘_ j i) k
  a = S._∙_ (S.const (S.comp-assoc f' g' h')) (S._⋆_ (S._⋆_ gamma beta) alpha)
  b = S._∙_ (S._⋆_ gamma (S._⋆_ beta alpha)) (S.const (S.comp-assoc f g h))
  a' = T.const (T.comp-assoc (map f') (map g') (map h')) ∙ ((family gamma ⋆ family beta) ⋆ family alpha)
  b' = (family gamma ⋆ (family beta ⋆ family alpha)) ∙ T.const (T.comp-assoc (map f) (map g) (map h))
  adjust = conjugate (L f g h) (R f' g' h')
  output = adjust ∘ phi (S._∘_ (S._∘_ h g) f) (S._∘_ h' (S._∘_ g' f'))

  opaque
    assoc-square : (i : S.MAP B C) (j : S.MAP C D) (k : S.MAP D E)
      → T._=₂_ (R i j k ∙ term (S.comp-assoc i j k)) (T.comp-assoc (map i) (map j) (map k) ∙ L i j k)
    assoc-square i j k =
      isoComp-cong (isoComp-cong (hcomp-idOuter (map k) (comp i j)) (T.idIso _)) (T.idIso _) then
      isoComp-assoc-at (map k ◁ comp i j) (comp (S._∘_ j i) k) (term (S.comp-assoc i j k)) then
      OperationCompatibility.associator K i j k then
      isoComp-cong (T.idIso _) (isoComp-cong ((hcomp-idInner (comp j k) (map i)) ⁻¹) (T.idIso _))
    left-horizontal : T._=₁_ (T.const (L f' g' h') ∙ family (S._⋆_ (S._⋆_ gamma beta) alpha))
      (((family gamma ⋆ family beta) ⋆ family alpha) ∙ T.const (L f g h))
    left-horizontal = Horizontal.horizontal-square W K (T.idIso (map f)) (T.idIso (map f'))
      (comp g h) (comp g' h') alpha (family alpha) (S._⋆_ gamma beta) (family gamma ⋆ family beta)
      (Horizontal.unchanged W K (family alpha)) (Horizontal.raw W K gamma beta)
    right-horizontal : T._=₁_ (T.const (R f' g' h') ∙ family (S._⋆_ gamma (S._⋆_ beta alpha)))
      ((family gamma ⋆ (family beta ⋆ family alpha)) ∙ T.const (R f g h))
    right-horizontal = Horizontal.horizontal-square W K (comp f g) (comp f' g')
      (T.idIso (map h)) (T.idIso (map h')) (S._⋆_ beta alpha) (family beta ⋆ family alpha) gamma (family gamma)
      (Horizontal.raw W K beta alpha) (Horizontal.unchanged W K (family gamma))
    left : T._=₁_ (output ∘ map a) a'
    left = T.comp-assoc (map a) (phi (S._∘_ (S._∘_ h g) f) (S._∘_ h' (S._∘_ g' f'))) adjust then
      Squares.solve T (L f g h) (R f' g' h') (family a) a'
        (Pasting.vertical W K (L f g h) (L f' g' h') (R f' g' h')
          (S._⋆_ (S._⋆_ gamma beta) alpha) (S.const (S.comp-assoc f' g' h'))
          ((family gamma ⋆ family beta) ⋆ family alpha) (T.const (T.comp-assoc (map f') (map g') (map h')))
          left-horizontal (Pasting.constant W K (L f' g' h') (R f' g' h')
            (S.comp-assoc f' g' h') (T.comp-assoc (map f') (map g') (map h')) (assoc-square f' g' h')))
    right : T._=₁_ (output ∘ map b) b'
    right = T.comp-assoc (map b) (phi (S._∘_ (S._∘_ h g) f) (S._∘_ h' (S._∘_ g' f'))) adjust then
      Squares.solve T (L f g h) (R f' g' h') (family b) b'
        (Pasting.vertical W K (L f g h) (R f g h) (R f' g' h')
          (S.const (S.comp-assoc f g h)) (S._⋆_ gamma (S._⋆_ beta alpha))
          (T.const (T.comp-assoc (map f) (map g) (map h))) (family gamma ⋆ (family beta ⋆ family alpha))
          (Pasting.constant W K (L f g h) (R f g h) (S.comp-assoc f g h)
            (T.comp-assoc (map f) (map g) (map h)) (assoc-square f g h)) right-horizontal)
    target : T._=₁_ a' b'
    target = Parameterized.horizontal-assoc T (family gamma) (family beta) (family alpha)
  module Law = FamilyWitness W a b output a' b' left right
```
