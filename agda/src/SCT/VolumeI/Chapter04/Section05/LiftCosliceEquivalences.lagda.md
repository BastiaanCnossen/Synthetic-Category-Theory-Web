# The coslice universal property of a chosen lift

The lifting adjunction gives a relative coslice equivalence after
restricting its target to identity arrows. Squares into identities are
the coslice of the lifted arrow's target. Their composite is therefore an
equivalence over the category of targets.

This proves the relative universal property with its literal comma
category as target. Computing that comma category as a pullback of two
ordinary coslices is a separate geometric lemma.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section05.LiftCosliceEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section03.RelativeSlices 𝒯 M ℱ P I using (module RelativeCoslice)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
  using (FunctorOver; compose-over)
import SCT.VolumeI.Chapter04.Section04.SquaresToIdentity as Identity
import SCT.VolumeI.Chapter04.Section04.CosliceAdjunctions as Coslices
import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences as Relative

module Covariant {C D : CAT} (p : MAP C D) (w : Fibration.CocartesianFibration p) where
  private
    module Eval = Evaluation p using (directed-ev₀; module Left)
    module W = Fibration.CocartesianFibration w using (lift; left-adjoint-section)
    module A = LeftAdjointSection W.left-adjoint-section using (adjunction)

  module At (b : Obj-abs Eval.Left.category) where
    arrow : Obj-abs (Ar C)
    arrow = W.lift ∘ b
    module Target = RelativeCoslice (Eval.directed-ev₀ ∘ identityArrow) b
    private
      module Fill = Identity.At 𝒯 M ℱ P I E S Q R arrow
        using (filling; filling-isEquiv; over-base)
      module Lift = Coslices.At 𝒯 M ℱ P I E S Q A.adjunction b identityArrow
        using (functor; isEquiv; over-base)

    over-base : FunctorOver (coslice-projection (ev₁ ∘ arrow)) Target.projection
    over-base = compose-over Lift.over-base Fill.over-base

    functor : MAP (Coslice C (ev₁ ∘ arrow)) Target.category
    functor = FunctorLift.lift over-base

    abstract
      isEquiv : IsEquiv functor
      isEquiv = equiv-compose Fill.filling Lift.functor
        Fill.filling-isEquiv Lift.isEquiv

    equivalence : Equiv (Coslice C (ev₁ ∘ arrow)) Target.category
    equivalence = record { functor = functor ; isEquiv = isEquiv }

    private
      module Inverse = Relative.Inverse 𝒯 M ℱ P over-base isEquiv
        using (inverse; left-inverse; right-inverse)
    open Inverse public renaming
      (inverse to inverse-over-base; left-inverse to left-inverse-over-base;
       right-inverse to right-inverse-over-base)
```
