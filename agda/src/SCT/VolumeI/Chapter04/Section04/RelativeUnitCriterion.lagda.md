# The unit and counit conditions over a base

For a fixed adjunction between specified functors over a base, the counit
lies over that base if and only if the unit does. The two implications in
`prop:Relative_Adjunction_Unit_Formulation` use only the triangle identities
and the full relative endpoint comparisons. They retain the same underlying
adjunction. No equivalence between animae of all such structured data is
claimed here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.RelativeUnitCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.RelativeAdjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
  using (identity-iso-over; inverse-iso-over; associator-over; left-unit-over; right-unit-over)
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismWhiskering as Whiskering
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismRetargeting as Retargeting
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismPostcomposition as Post
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismTriangles as Triangles

module At {C D B : CAT} (p : MAP C B) (q : MAP D B)
  (L : FunctorOver p q) (R : FunctorOver q p)
  (adj : Adjunction (FunctorLift.lift L) (FunctorLift.lift R)) where
  private
    module A = Adjunction adj
    module LL = FunctorLift L
    module RR = FunctorLift R
    module ChangeL = Retargeting.OverBase 𝒯 M ℱ P I E S p q
    module ChangeR = Retargeting.OverBase 𝒯 M ℱ P I E S q p
  left-middle = compose-over (compose-over L R) L
  right-middle = compose-over (compose-over R L) R
  UnitOver = Over.IsOver p p (identity-over p) (compose-over R L) A.unit
  CounitOver = Over.IsOver q q (compose-over L R) (identity-over q) A.counit

  module FromCounit (over : CounitOver) where
    relative-counit : Over.MorphismOver q q (compose-over L R) (identity-over q)
    relative-counit = record { underlying = A.counit ; over-base = over }
    private module Restrict = Whiskering.Pre 𝒯 M ℱ P I E S L relative-counit

    abstract
      left-counit-over : Over.IsOver p q left-middle L A.left-counit
      left-counit-over = ChangeL.retarget-isOver (restrict-expression A.counit LL.lift)
        (identity-iso-over left-middle) (left-unit-over L) Restrict.over-base

      left-unit-over-base : Over.IsOver p q L left-middle A.left-unit
      left-unit-over-base = Triangles.Triangle.first-over 𝒯 M ℱ P I E S
        {u = L} {v = left-middle} A.left-unit A.left-counit A.left-triangle left-counit-over

      unit-over : UnitOver
      unit-over = Post.At.reflects 𝒯 M ℱ P I E S L
        {u = identity-over p} {v = compose-over R L} A.unit
        (ChangeL.retarget-reflects (post-expression LL.lift A.unit)
          (right-unit-over L) (inverse-iso-over (associator-over L R L)) left-unit-over-base)

  module FromUnit (over : UnitOver) where
    relative-unit : Over.MorphismOver p p (identity-over p) (compose-over R L)
    relative-unit = record { underlying = A.unit ; over-base = over }
    private module Restrict = Whiskering.Pre 𝒯 M ℱ P I E S R relative-unit

    abstract
      right-unit-over-base : Over.IsOver q p R right-middle A.right-unit
      right-unit-over-base = ChangeR.retarget-isOver (restrict-expression A.unit RR.lift)
        (left-unit-over R) (identity-iso-over right-middle) Restrict.over-base

      right-counit-over : Over.IsOver q p right-middle R A.right-counit
      right-counit-over = Triangles.Triangle.second-over 𝒯 M ℱ P I E S
        {u = R} {v = right-middle} A.right-unit A.right-counit A.right-triangle right-unit-over-base

      counit-over : CounitOver
      counit-over = Post.At.reflects 𝒯 M ℱ P I E S R
        {u = compose-over L R} {v = identity-over q} A.counit
        (ChangeR.retarget-reflects (post-expression RR.lift A.counit)
          (inverse-iso-over (associator-over R L R)) (right-unit-over R) right-counit-over)

counit-to-unit : {C D B : CAT} {p : MAP C B} {q : MAP D B}
  {L : FunctorOver p q} {R : FunctorOver q p} → RelativeAdjunction p q L R → UnitRelativeAdjunction p q L R
counit-to-unit {p = p} {q} {L} {R} w = record
  { adjunction = W.adjunction
  ; unit-over-base = At.FromCounit.unit-over p q L R W.adjunction W.counit-over-base }
  where module W = RelativeAdjunction w

unit-to-counit : {C D B : CAT} {p : MAP C B} {q : MAP D B}
  {L : FunctorOver p q} {R : FunctorOver q p} → UnitRelativeAdjunction p q L R → RelativeAdjunction p q L R
unit-to-counit {p = p} {q} {L} {R} w = record
  { adjunction = W.adjunction
  ; counit-over-base = At.FromUnit.counit-over p q L R W.adjunction W.unit-over-base }
  where module W = UnitRelativeAdjunction w
```
