# Sections of a constant family

The equivalence `Π (W C) ≃ Fun A C` follows from the two dependent
universal properties and the equivalence `Σ (W R) ≃ A × R`. The
comparison is tested on arbitrary category parameters.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as ProductAction
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.LeftCurrying as LeftCurrying
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.Representations as Representations
import SCT.VolumeI.Chapter05.Section03.ConstantFamilies as Constants
import SCT.VolumeI.Chapter05.Section03.ConstantFamilyNaturality as Naturality

module SCT.VolumeI.Chapter05.Section05.ConstantSections
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (C : View.CAT S) where

private
  module S = View S
  module T = View T
module W = Weakening W
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module PA = ProductAction W P using (curry-η; curry-cong; curry-pre)
module QA = SumAction W P Q using (extend-η; extend-cong; Σ-map; flatten-local-pre)
module L = LeftCurrying S MS FS using (curry; uncurry; curry-β; curry-η; curry-cong; uncurry-cong; uncurry-pre)
module N = Naturality W P Q A e using (comparison; naturality)
open Functors.FunctorCategories FS using (Fun)
open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus S using (_then_)
open ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)

base : S.CAT
base = S.AN.category A

χ : (R : S.CAT) → S.MAP (Q.Σ (W.cat R)) (S._×_ base R)
χ = N.comparison

χ-equiv : (R : S.CAT) → S.IsEquiv (χ R)
χ-equiv R = Constants.comparison-isEquiv W WP MS MT FS FT K P Q A e R

χ⁻¹ : (R : S.CAT) → S.MAP (S._×_ base R) (Q.Σ (W.cat R))
χ⁻¹ R = S.IsEquiv.inverse (χ-equiv R)

cancel-section : {D R : S.CAT} (f : S.MAP (Q.Σ (W.cat R)) D)
  → S._=₁_ ((f ∘ χ⁻¹ R) ∘ χ R) f
cancel-section {R = R} f = S.comp-assoc (χ R) (χ⁻¹ R) f then
  (f ◁ (S.IsEquiv.sectionIso (χ-equiv R)) ⁻¹) then S.comp-unitʳ f

cancel-retraction : {D R : S.CAT} (f : S.MAP (S._×_ base R) D)
  → S._=₁_ ((f ∘ χ R) ∘ χ⁻¹ R) f
cancel-retraction {R = R} f = S.comp-assoc (χ⁻¹ R) (χ R) f then
  (f ◁ (S.IsEquiv.retractionIso (χ-equiv R)) ⁻¹) then S.comp-unitʳ f

un-cong : {R : S.CAT} {h k : S.MAP R (P.Π (W.cat C))}
  → S._=₁_ h k → T._=₁_ (P.uncurry h) (P.uncurry k)
un-cong α = T._◁_ (P.evaluation (W.cat C)) (W.term α)

flat-cong : {R : S.CAT} {h k : S.MAP (Q.Σ (W.cat R)) C}
  → S._=₁_ h k → T._=₁_ (Q.flatten h) (Q.flatten k)
flat-cong {R} α = T._▷_ (W.term α) (Q.pair (W.cat R))

forth : {R : S.CAT} → S.MAP R (P.Π (W.cat C)) → S.MAP R (Fun base C)
forth {R} h = L.curry (Q.extend (P.uncurry h) ∘ χ⁻¹ R)

back : {R : S.CAT} → S.MAP R (Fun base C) → S.MAP R (P.Π (W.cat C))
back {R} k = P.curry (Q.flatten (L.uncurry k ∘ χ R))

forth-cong : {R : S.CAT} {h k : S.MAP R (P.Π (W.cat C))}
  → S._=₁_ h k → S._=₁_ (forth h) (forth k)
forth-cong {R} α = L.curry-cong (QA.extend-cong (un-cong α) ▷ χ⁻¹ R)

back-cong : {R : S.CAT} {h k : S.MAP R (Fun base C)}
  → S._=₁_ h k → S._=₁_ (back h) (back k)
back-cong {R} α = PA.curry-cong (flat-cong (L.uncurry-cong α ▷ χ R))

back-forth : {R : S.CAT} (h : S.MAP R (P.Π (W.cat C))) → S._=₁_ (back (forth h)) h
back-forth {R} h = PA.curry-cong
  (T._∙_ (T._⁻¹ (Q.extend-β (P.uncurry h)))
    (flat-cong ((L.curry-β (Q.extend (P.uncurry h) ∘ χ⁻¹ R) ▷ χ R) then
      cancel-section (Q.extend (P.uncurry h))))) then PA.curry-η h

forth-back : {R : S.CAT} (k : S.MAP R (Fun base C)) → S._=₁_ (forth (back k)) k
forth-back {R} k = L.curry-cong
  ((QA.extend-cong (T._⁻¹ (P.curry-β (Q.flatten (L.uncurry k ∘ χ R)))) ▷ χ⁻¹ R) then
   (QA.extend-η (L.uncurry k ∘ χ R) ▷ χ⁻¹ R) then
   cancel-retraction (L.uncurry k)) then L.curry-η k

back-pre : {R D : S.CAT} (k : S.MAP D (Fun base C)) (r : S.MAP R D)
  → S._=₁_ (back (k ∘ r)) (back k ∘ r)
back-pre {R} {D} k r = PA.curry-cong
  (T._∙_ (QA.flatten-local-pre (L.uncurry k ∘ χ D) (W.map r))
    (flat-cong ((L.uncurry-pre k r ▷ χ R) then
      S.comp-assoc (χ R) (productMap (S.id base) r) (L.uncurry k) then
      (L.uncurry k ◁ (N.naturality r) ⁻¹) then
      (S.comp-assoc (QA.Σ-map (W.map r)) (χ D) (L.uncurry k)) ⁻¹))) then
  PA.curry-pre (Q.flatten (L.uncurry k ∘ χ D)) r

module Comparison = Representations.CompareCategories S (P.Π (W.cat C)) (Fun base C)
  forth back forth-cong back-cong back-forth forth-back back-pre
  using (F; G; left-inverse; right-inverse; isEquiv; equivalence)

evaluation-total : S._=₁_
  (L.uncurry Comparison.F ∘ χ (P.Π (W.cat C))) (Q.extend (P.evaluation (W.cat C)))
evaluation-total = (L.curry-β (Q.extend (P.uncurry (S.id (P.Π (W.cat C)))) ∘
    χ⁻¹ (P.Π (W.cat C))) ▷ χ (P.Π (W.cat C))) then
  cancel-section (Q.extend (P.uncurry (S.id (P.Π (W.cat C))))) then
  QA.extend-cong (T._∙_ (T.comp-unitʳ (P.evaluation (W.cat C)))
    (T._◁_ (P.evaluation (W.cat C)) (W.unit (P.Π (W.cat C)))))

evaluation-local : T._=₁_
  (Q.flatten (L.uncurry Comparison.F ∘ χ (P.Π (W.cat C)))) (P.evaluation (W.cat C))
evaluation-local = T._∙_ (T._⁻¹ (Q.extend-β (P.evaluation (W.cat C)))) (flat-cong evaluation-total)
```
