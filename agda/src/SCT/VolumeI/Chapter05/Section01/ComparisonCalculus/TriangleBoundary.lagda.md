# Transporting the triangle boundary

The two triangle paths are normalized from operation compatibility. Their comparison transports the source witness without asserting its agreement with the selected target witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Triangle as Triangle

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.TriangleBoundary {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W)
  {C D E : View.CAT S} (f : View.MAP S C D) (g : View.MAP S D E) where
private
  module S = View S
  module T = View T
  module P = Triangle W f g
  module SC = Calculus S using (hcomp-idOuter; hcomp-idInner; isoComp-cong)
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T

short-square : T._=₂_ (P.right-compositor ∙ term P.source-short)
  (P.target-short ∙ P.left-compositor)
short-square =
  isoComp-cong (T.idIso _) (cell2 (SC.hcomp-idInner (S.comp-unitʳ g) f)) then
  Operations.pre-term-square W K f (S.comp-unitʳ g) then
  isoComp-cong (T.preWhisker (map f) ◁ OperationCompatibility.rightUnit K g) (T.idIso _) then
  isoComp-cong (preWhisker-isoComp-at (T.comp-unitʳ (map g))
    (S-unit-compositor) (map f)) (T.idIso _) then
  isoComp-assoc-at _ _ _ then
  isoComp-cong ((hcomp-idInner (T.comp-unitʳ (map g)) (map f)) ⁻¹)
    (isoComp-cong (preWhisker-isoComp-at (map g ◁ unit D) (comp (S.id D) g) (map f)) (T.idIso _) then
      isoComp-assoc-at _ _ _)
  where
  S-unit-compositor = (map g ◁ unit D) ∙ comp (S.id D) g

long-whiskered : T._=₂_
  (P.right-compositor ∙ term (S._∙_ (S._◁_ g (S.comp-unitˡ f)) (S.comp-assoc f (S.id D) g)))
  (((map g ◁ T.comp-unitˡ (map f)) ∙ T.comp-assoc (map f) (T.id (cat D)) (map g)) ∙ P.left-compositor)
long-whiskered =
  isoComp-cong (T.idIso _) (Operations.vertical-term W K _ _) then
  (isoComp-assoc-at _ _ _) ⁻¹ then
  isoComp-cong (Operations.post-term-square W K g (S.comp-unitˡ f)) (T.idIso _) then
  isoComp-assoc-at _ _ _ then
  isoComp-cong (T.postWhisker (map g) ◁ OperationCompatibility.leftUnit K f) (T.idIso _) then
  isoComp-cong (postWhisker-isoComp-at (map g) (T.comp-unitˡ (map f))
    ((unit D ▷ map f) ∙ comp f (S.id D))) (T.idIso _) then
  isoComp-assoc-at _ _ _ then
  isoComp-cong (T.idIso _)
    (isoComp-cong (postWhisker-isoComp-at (map g) (unit D ▷ map f) (comp f (S.id D))) (T.idIso _) then
      isoComp-assoc-at _ _ _ then
      isoComp-cong (T.idIso _) (OperationCompatibility.associator K f (S.id D) g) then
      (isoComp-assoc-at _ _ _) ⁻¹ then
      isoComp-cong ((whisker-mixed-at (unit D) (map f) (map g)) ⁻¹) (T.idIso _) then
      isoComp-assoc-at _ _ _) then
  (isoComp-assoc-at _ _ _) ⁻¹

long-square : T._=₂_ (P.right-compositor ∙ term P.source-long)
  (P.target-long ∙ P.left-compositor)
long-square =
  isoComp-cong (T.idIso _) (cell2 (SC.isoComp-cong (SC.hcomp-idOuter g (S.comp-unitˡ f)) (S.idIso _))) then
  long-whiskered then
  isoComp-cong (isoComp-cong ((hcomp-idOuter (map g) (T.comp-unitˡ (map f))) ⁻¹) (T.idIso _)) (T.idIso _)

boundaries : P.BoundaryNormalization
boundaries = record
  { short = Squares.term-solve T P.left-compositor P.right-compositor _ _ short-square
  ; long = Squares.term-solve T P.left-compositor P.right-compositor _ _ long-square }

-- These boundary proofs use neither chosen triangle witness.
opaque
  transported-triangle : T._=₂_ P.target-short P.target-long
  transported-triangle = P.normalized boundaries

  transported-triangle-expansion : T._=₃_ transported-triangle (P.normalized boundaries)
  transported-triangle-expansion = T.idIso transported-triangle
```
