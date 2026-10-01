# Adjunction data over a base

These records encode the normalized over-base condition in
`def:Relative_Adjunction`, using the specified structure identifications
of both relative functors. The unit-based record states the alternative
condition; the equivalence of the two formulations is a separate theorem.
The interpretation as arrows in the chosen `FunOver` also requires the
relative-expression comparison and is not asserted by these records alone.

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

module SCT.VolumeI.Chapter04.Section04.RelativeAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S
  public using (FunctorOver; identity-over; compose-over; module Over)

record RelativeAdjunction {C D B : CAT} (p : MAP C B) (q : MAP D B)
  (L : FunctorOver p q) (R : FunctorOver q p) : Set m where
  field
    adjunction : Adjunction (FunctorLift.lift L) (FunctorLift.lift R)
    counit-over-base : Over.IsOver q q (compose-over L R) (identity-over q) (Adjunction.counit adjunction)

  counit : Over.MorphismOver q q (compose-over L R) (identity-over q)
  counit = record { underlying = Adjunction.counit adjunction ; over-base = counit-over-base }

record UnitRelativeAdjunction {C D B : CAT} (p : MAP C B) (q : MAP D B)
  (L : FunctorOver p q) (R : FunctorOver q p) : Set m where
  field
    adjunction : Adjunction (FunctorLift.lift L) (FunctorLift.lift R)
    unit-over-base : Over.IsOver p p (identity-over p) (compose-over R L) (Adjunction.unit adjunction)

  unit : Over.MorphismOver p p (identity-over p) (compose-over R L)
  unit = record { underlying = Adjunction.unit adjunction ; over-base = unit-over-base }

record RelativeLeftAdjointSection {C D B : CAT} (p : MAP C B) (q : MAP D B)
  (f : FunctorOver p q) (s : FunctorOver q p) : Set m where
  field
    relative-adjunction : RelativeAdjunction q p s f
    unit-invertible : IsInvertibleExpression (Adjunction.unit (RelativeAdjunction.adjunction relative-adjunction))

  absolute : LeftAdjointSection (FunctorLift.lift f) (FunctorLift.lift s)
  absolute = record { adjunction = RelativeAdjunction.adjunction relative-adjunction ; unit-invertible = unit-invertible }

record RelativeRightAdjointSection {C D B : CAT} (p : MAP C B) (q : MAP D B)
  (f : FunctorOver p q) (s : FunctorOver q p) : Set m where
  field
    relative-adjunction : RelativeAdjunction p q f s
    counit-invertible : IsInvertibleExpression (Adjunction.counit (RelativeAdjunction.adjunction relative-adjunction))

  absolute : RightAdjointSection (FunctorLift.lift f) (FunctorLift.lift s)
  absolute = record { adjunction = RelativeAdjunction.adjunction relative-adjunction ; counit-invertible = counit-invertible }
```
