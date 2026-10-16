# Detecting equivalences with mapping animae

A functor is an equivalence if its postcomposition maps on mapping animae
are equivalences when tested at its source and target. The dual pair of
precomposition tests also suffices. Naming and decoding connect these
internal tests with the external inverse functor.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.EquivalenceDetection where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-reflect; Section; Retraction)
open import SCT.VolumeI.Chapter01.Section03.Factorizations
  using (Factorization; factor; triangle; factor-through-equiv)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Points
  using (name; decode; name⁼; name-reflect; name-decode)
open import SCT.VolumeI.Chapter01.Section04.Functoriality
  using (mapPost; mapPre; mapPost-name; mapPre-name)
```

## Reflecting identifications of functors

The structural source and target categories remain explicit. Reflection in
the mapping anima is transported through the actual naming operation.

```agda
module _ {Γ : Context} where
  mapPost-reflect : {B C D : CAT Γ} (f : MAP C D)
    → IsEquiv (mapPost {C = B} f)
    → (g h : MAP B C) → (f ∘ g) =₁ (f ∘ h) → g =₁ h
  mapPost-reflect f e g h α = name-reflect g h (equiv-reflect e (name g) (name h)
    ((mapPost-name f h) ⁻¹ ∙ (name⁼ α ∙ mapPost-name f g)))

  mapPre-reflect : {B C D : CAT Γ} (f : MAP B C)
    → IsEquiv (mapPre {D = D} f)
    → (g h : MAP C D) → (g ∘ f) =₁ (h ∘ f) → g =₁ h
  mapPre-reflect f e g h α = name-reflect g h (equiv-reflect e (name g) (name h)
    ((mapPre-name f h) ⁻¹ ∙ (name⁼ α ∙ mapPre-name f g)))

```

## Obtaining one-sided inverses

The target test factors the named identity through postcomposition. Decoding
its factor gives a section, and the naming comparison supplies its law.
Dually, the source test for precomposition produces a retraction. These
are genuine absolute points, rather than arbitrary test terms. The recovered
identification now uses the canonical `name-reflect` from Points; agreement
with the first rebuild's discarded recovery choice is not asserted.

```agda
  mapPost-section : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv (mapPost {C = D} f) → Section f
  mapPost-section {C} {D} f e = record
    { section = decode point
    ; section-law = (name-reflect _ _
        (triangle chosen ∙
          ((mapPost f ◁ name-decode point) ∙ (mapPost-name f (decode point)) ⁻¹))) ⁻¹
    }
    where
    chosen : Factorization (mapPost f) (name (id D))
    chosen = factor-through-equiv e (name (id D))
    point : Obj-abs (Map D C)
    point = factor chosen

  mapPre-retraction : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv (mapPre {D = C} f) → Retraction f
  mapPre-retraction {C} {D} f e = record
    { retraction = decode point
    ; retraction-law = (name-reflect _ _
        (triangle chosen ∙
          ((mapPre f ◁ name-decode point) ∙ (mapPre-name f (decode point)) ⁻¹))) ⁻¹
    }
    where
    chosen : Factorization (mapPre f) (name (id C))
    chosen = factor-through-equiv e (name (id C))
    point : Obj-abs (Map D C)
    point = factor chosen

```

## Only the source and target tests are needed

For postcomposition, the target test constructs a section and the source
test reflects its other inverse law. The dual argument starts with a
retraction. The explicit two-test statements expose the proof rather than
hiding it behind a quantifier over all categories.

```agda
  post-tests-isEquiv : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv (mapPost {C = C} f) → IsEquiv (mapPost {C = D} f) → IsEquiv f
  post-tests-isEquiv {C} {D} f source-test target-test = record
    { inverse = g
    ; left-inverse-law = (mapPost-reflect f source-test (g ∘ f) (id C)
        ((comp-unitʳ f) ⁻¹ ∙
          (comp-unitˡ f ∙ (((Section.section-law s) ⁻¹ ▷ f) ∙ (comp-assoc f g f) ⁻¹)))) ⁻¹
    ; right-inverse-law = Section.section-law s
    }
    where
    s : Section f
    s = mapPost-section f target-test
    g : MAP D C
    g = Section.section s

  pre-tests-isEquiv : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv (mapPre {D = C} f) → IsEquiv (mapPre {D = D} f) → IsEquiv f
  pre-tests-isEquiv {C} {D} f source-test target-test = record
    { inverse = g
    ; left-inverse-law = Retraction.retraction-law r
    ; right-inverse-law = (mapPre-reflect f target-test (f ∘ g) (id D)
        ((comp-unitˡ f) ⁻¹ ∙
          (comp-unitʳ f ∙ ((f ◁ (Retraction.retraction-law r) ⁻¹) ∙ comp-assoc f g f)))) ⁻¹
    }
    where
    r : Retraction f
    r = mapPre-retraction f source-test
    g : MAP D C
    g = Retraction.retraction r

```

## All-category and anima tests

The all-category criteria instantiate the tests at the source and target.
Testing only on animae gives the same conclusion here only when both source
and target are animae. No detection theorem for arbitrary categories from
anima probes is asserted.

```agda
  post-tests-all : {C D : CAT Γ} (f : MAP C D)
    → ((E : CAT Γ) → IsEquiv (mapPost {C = E} f)) → IsEquiv f
  post-tests-all {C} {D} f tests = post-tests-isEquiv f (tests C) (tests D)

  pre-tests-all : {C D : CAT Γ} (f : MAP C D)
    → ((E : CAT Γ) → IsEquiv (mapPre {D = E} f)) → IsEquiv f
  pre-tests-all {C} {D} f tests = pre-tests-isEquiv f (tests C) (tests D)

  post-tests-animae : {C D : CAT Γ} → isAn C → isAn D → (f : MAP C D)
    → ((E : CAT Γ) → isAn E → IsEquiv (mapPost {C = E} f)) → IsEquiv f
  post-tests-animae {C} {D} cAn dAn f tests = post-tests-isEquiv f (tests C cAn) (tests D dAn)

  pre-tests-animae : {C D : CAT Γ} → isAn C → isAn D → (f : MAP C D)
    → ((E : CAT Γ) → isAn E → IsEquiv (mapPre {D = E} f)) → IsEquiv f
  pre-tests-animae {C} {D} cAn dAn f tests = pre-tests-isEquiv f (tests C cAn) (tests D dAn)
```
