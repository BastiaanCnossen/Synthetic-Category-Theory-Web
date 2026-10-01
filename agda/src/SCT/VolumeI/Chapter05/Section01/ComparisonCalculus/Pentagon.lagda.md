# The two pentagon paths

This module displays the parenthesized functor expressions and the short and long identification paths of the pentagon. Their weakened endpoints have explicit compositors.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Pentagon {l : Level} {S T : Theory l l l} (W : Weakening S T)
  {A B C D E : View.CAT S}
  (f : View.MAP S A B) (g : View.MAP S B C)
  (h : View.MAP S C D) (k : View.MAP S D E) where

private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)

source-left : S.MAP A E
source-left = S._∘_ (S._∘_ (S._∘_ k h) g) f
source-right : S.MAP A E
source-right = S._∘_ k (S._∘_ h (S._∘_ g f))
target-left : T.MAP (cat A) (cat E)
target-left = ((map k ∘ map h) ∘ map g) ∘ map f
target-right : T.MAP (cat A) (cat E)
target-right = map k ∘ (map h ∘ (map g ∘ map f))

left-compositor : T._=₁_ (map source-left) target-left
left-compositor = ((comp h k ▷ map g) ▷ map f) ∙
  ((comp g (S._∘_ k h) ▷ map f) ∙ comp f (S._∘_ (S._∘_ k h) g))
right-compositor : T._=₁_ (map source-right) target-right
right-compositor = (map k ◁ (map h ◁ comp f g)) ∙
  ((map k ◁ comp (S._∘_ g f) h) ∙ comp (S._∘_ h (S._∘_ g f)) k)

source-short source-long : S._=₁_ source-left source-right
source-short = S._∙_ (S.comp-assoc (S._∘_ g f) h k) (S.comp-assoc f g (S._∘_ k h))
source-long = S._∙_ (S._∙_ (S._⋆_ (S.idIso k) (S.comp-assoc f g h))
                            (S.comp-assoc f (S._∘_ h g) k))
                     (S._⋆_ (S.comp-assoc g h k) (S.idIso f))

target-short target-long : T._=₁_ target-left target-right
target-short = T.comp-assoc (map g ∘ map f) (map h) (map k) ∙
  T.comp-assoc (map f) (map g) (map k ∘ map h)
target-long = (T._⋆_ (T.idIso (map k)) (T.comp-assoc (map f) (map g) (map h)) ∙
  T.comp-assoc (map f) (map h ∘ map g) (map k)) ∙
  T._⋆_ (T.comp-assoc (map g) (map h) (map k)) (T.idIso (map f))

adjust : T.MAP (T._＝_ (map source-left) (map source-right)) (T._＝_ target-left target-right)
adjust = Boundaries.conjugate W left-compositor right-compositor

normalized-short normalized-long : T._=₁_ target-left target-right
normalized-short = adjust ∘ term source-short
normalized-long = adjust ∘ term source-long

transported : T._=₂_ normalized-short normalized-long
transported = adjust ◁ cell2 (S.comp-pentagon f g h k)

-- Boundary data are separated from the minimal core. PentagonBoundary derives
-- both fields from OperationCompatibility, without using either pentagon witness.
record BoundaryNormalization : Set l where
  field
    short : T._=₂_ normalized-short target-short
    long : T._=₂_ normalized-long target-long

normalized : BoundaryNormalization → T._=₂_ target-short target-long
normalized b = BoundaryNormalization.long b ∙
  (transported ∙ (BoundaryNormalization.short b) ⁻¹)

-- Preserving a specified pentagon is a further, three-dimensional condition.
-- Merely producing 'normalized b' is not this condition. The derived boundary
-- record from PentagonBoundary is available as a concrete choice of b.
record PreservesChosenPentagon (b : BoundaryNormalization) : Set l where
  field
    comparison : T._=₃_ (normalized b) (T.comp-pentagon (map f) (map g) (map h) (map k))
```
