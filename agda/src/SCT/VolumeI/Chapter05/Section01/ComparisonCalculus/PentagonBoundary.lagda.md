# Transporting the pentagon boundary

Operation compatibility compares the short and long paths separately. These boundary comparisons transport the source pentagonator into the type of the target pentagonator; equality with the selected target remains additional data.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Pasting as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Pentagon as Pentagon

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.PentagonBoundary {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W)
  {A B C D E : View.CAT S}
  (f : View.MAP S A B) (g : View.MAP S B C)
  (h : View.MAP S C D) (k : View.MAP S D E) where
private
  module S = View S
  module T = View T
  module P = Pentagon W f g h k
  module SC = Calculus S using (hcomp-idOuter; hcomp-idInner)
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T

-- The fifth parenthesization on the short side of the pentagon.
short-middle : T._=₁_ (map (S._∘_ (S._∘_ k h) (S._∘_ g f)))
  ((map k ∘ map h) ∘ (map g ∘ map f))
short-middle = (comp h k ▷ (map g ∘ map f)) ∙
  ((map (S._∘_ k h) ◁ comp f g) ∙ comp (S._∘_ g f) (S._∘_ k h))

short-first : T._=₂_ (short-middle ∙ term (S.comp-assoc f g (S._∘_ k h)))
  (T.comp-assoc (map f) (map g) (map k ∘ map h) ∙ P.left-compositor)
short-first = decorate-square _ _ _ _ _ _ _ _
  (OperationCompatibility.associator K f g (S._∘_ k h))
  ((preWhisker-comp-at (comp h k) (map g) (map f)) ⁻¹)

short-second : T._=₂_ (P.right-compositor ∙ term (S.comp-assoc (S._∘_ g f) h k))
  (T.comp-assoc (map g ∘ map f) (map h) (map k) ∙ short-middle)
short-second = decorate-square _ _ _ _ _ _ _ _
  (OperationCompatibility.associator K (S._∘_ g f) h k)
  ((postWhisker-comp-at (comp f g) (map h) (map k)) ⁻¹) then
  isoComp-cong (T.idIso _)
    ((isoComp-assoc-at ((map k ∘ map h) ◁ comp f g)
        (comp h k ▷ map (S._∘_ g f)) (comp (S._∘_ g f) (S._∘_ k h))) ⁻¹ then
      isoComp-cong ((interchange-at (comp h k) (comp f g)) ⁻¹) (T.idIso _) then
      isoComp-assoc-at _ _ _)

short-square : T._=₂_ (P.right-compositor ∙ term P.source-short)
  (P.target-short ∙ P.left-compositor)
short-square = Pasting.vertical W K P.left-compositor short-middle P.right-compositor
  (S.comp-assoc f g (S._∘_ k h)) (S.comp-assoc (S._∘_ g f) h k)
  (T.comp-assoc (map f) (map g) (map k ∘ map h))
  (T.comp-assoc (map g ∘ map f) (map h) (map k)) short-first short-second

short : T._=₂_ P.normalized-short P.target-short
short = Squares.term-solve T P.left-compositor P.right-compositor _ _ short-square

-- The two intermediate parenthesizations on the long side.
long-first-compositor : T._=₁_ (map (S._∘_ (S._∘_ k (S._∘_ h g)) f))
  ((map k ∘ (map h ∘ map g)) ∘ map f)
long-first-compositor = ((map k ◁ comp g h) ▷ map f) ∙
  ((comp (S._∘_ h g) k ▷ map f) ∙ comp f (S._∘_ k (S._∘_ h g)))

long-second-compositor : T._=₁_ (map (S._∘_ k (S._∘_ (S._∘_ h g) f)))
  (map k ∘ ((map h ∘ map g) ∘ map f))
long-second-compositor = (map k ◁ (comp g h ▷ map f)) ∙
  ((map k ◁ comp f (S._∘_ h g)) ∙ comp (S._∘_ (S._∘_ h g) f) k)

long-middle : T._=₂_ (long-second-compositor ∙ term (S.comp-assoc f (S._∘_ h g) k))
  (T.comp-assoc (map f) (map h ∘ map g) (map k) ∙ long-first-compositor)
long-middle = decorate-square _ _ _ _ _ _ _ _
  (OperationCompatibility.associator K f (S._∘_ h g) k)
  ((whisker-mixed-at (comp g h) (map f) (map k)) ⁻¹)

long-first : T._=₂_
  (long-first-compositor ∙ term (S._⋆_ (S.comp-assoc g h k) (S.idIso f)))
  (T._⋆_ (T.comp-assoc (map g) (map h) (map k)) (T.idIso (map f)) ∙ P.left-compositor)
long-first = Squares.term-change T
  (Pasting.pre W K f _ _ (S.comp-assoc g h k) (T.comp-assoc (map g) (map h) (map k))
    (isoComp-assoc-at (map k ◁ comp g h) (comp (S._∘_ h g) k) (term (S.comp-assoc g h k)) then
      OperationCompatibility.associator K g h k))
  (isoComp-cong (preWhisker-isoComp-at (comp h k ▷ map g) (comp g (S._∘_ k h)) (map f)) (T.idIso _) then
    isoComp-assoc-at _ _ _)
  (isoComp-cong (preWhisker-isoComp-at (map k ◁ comp g h) (comp (S._∘_ h g) k) (map f)) (T.idIso _) then
    isoComp-assoc-at _ _ _)
  (cell2 ((SC.hcomp-idInner (S.comp-assoc g h k) f) S.⁻¹))
  ((hcomp-idInner (T.comp-assoc (map g) (map h) (map k)) (map f)) ⁻¹)

long-last : T._=₂_
  (P.right-compositor ∙ term (S._⋆_ (S.idIso k) (S.comp-assoc f g h)))
  (T._⋆_ (T.idIso (map k)) (T.comp-assoc (map f) (map g) (map h)) ∙ long-second-compositor)
long-last = Squares.term-change T
  (Pasting.post W K k _ _ (S.comp-assoc f g h) (T.comp-assoc (map f) (map g) (map h))
    (isoComp-assoc-at (map h ◁ comp f g) (comp (S._∘_ g f) h) (term (S.comp-assoc f g h)) then
      OperationCompatibility.associator K f g h))
  (isoComp-cong (postWhisker-isoComp-at (map k) (comp g h ▷ map f) (comp f (S._∘_ h g))) (T.idIso _) then
    isoComp-assoc-at _ _ _)
  (isoComp-cong (postWhisker-isoComp-at (map k) (map h ◁ comp f g) (comp (S._∘_ g f) h)) (T.idIso _) then
    isoComp-assoc-at _ _ _)
  (cell2 ((SC.hcomp-idOuter k (S.comp-assoc f g h)) S.⁻¹))
  ((hcomp-idOuter (map k) (T.comp-assoc (map f) (map g) (map h))) ⁻¹)

long-square : T._=₂_ (P.right-compositor ∙ term P.source-long)
  (P.target-long ∙ P.left-compositor)
long-square = Pasting.vertical W K P.left-compositor long-first-compositor P.right-compositor
  (S._⋆_ (S.comp-assoc g h k) (S.idIso f))
  (S._∙_ (S._⋆_ (S.idIso k) (S.comp-assoc f g h)) (S.comp-assoc f (S._∘_ h g) k))
  (T._⋆_ (T.comp-assoc (map g) (map h) (map k)) (T.idIso (map f)))
  (T._⋆_ (T.idIso (map k)) (T.comp-assoc (map f) (map g) (map h)) ∙
    T.comp-assoc (map f) (map h ∘ map g) (map k))
  long-first
  (Pasting.vertical W K long-first-compositor long-second-compositor P.right-compositor
    (S.comp-assoc f (S._∘_ h g) k) (S._⋆_ (S.idIso k) (S.comp-assoc f g h))
    (T.comp-assoc (map f) (map h ∘ map g) (map k))
    (T._⋆_ (T.idIso (map k)) (T.comp-assoc (map f) (map g) (map h))) long-middle long-last)

long : T._=₂_ P.normalized-long P.target-long
long = Squares.term-solve T P.left-compositor P.right-compositor _ _ long-square

boundaries : P.BoundaryNormalization
boundaries = record { short = short ; long = long }

-- Neither boundary proof uses the source or target pentagon witness.
-- Identifying the resulting transported pentagon with the selected target
-- witness is still the separate PreservesChosenPentagon condition.

opaque
  transported-pentagon : T._=₂_ P.target-short P.target-long
  transported-pentagon = P.normalized boundaries

  -- Expose the defining comparison without expanding the proof outside here.
  transported-pentagon-expansion : T._=₃_ transported-pentagon (P.normalized boundaries)
  transported-pentagon-expansion = T.idIso transported-pentagon
```
