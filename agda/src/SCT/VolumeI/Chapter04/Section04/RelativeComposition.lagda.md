# Composition of relative adjunctions

The counit of the composite absolute adjunction is a transformation over
the base. Its construction uses relative whiskering, composition, and
associators, and retains the specified structure identifications. This
proves the composition assertion in
`prop:Relative_Adjunctions_Compose_And_Base_Change` for the normalized
relative-expression formulation; base change is separate.

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

module SCT.VolumeI.Chapter04.Section04.RelativeComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.RelativeAdjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
  using (identity-iso-over; inverse-iso-over; associator-over; left-unit-over)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-inverse)
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismWhiskering as Whiskering
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismRetargeting as Retargeting
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeInterface as Absolute

module Composite {C D T B : CAT} {p : MAP C B} {q : MAP D B} {t : MAP T B}
  {L : FunctorOver p q} {R : FunctorOver q p} {K : FunctorOver q t} {U : FunctorOver t q}
  (adjA : RelativeAdjunction p q L R) (adjB : RelativeAdjunction q t K U) where
  private
    module A = RelativeAdjunction adjA
    module B′ = RelativeAdjunction adjB
    module AA = Adjunction A.adjunction
    module BB = Adjunction B′.adjunction
    module Pre = Whiskering.Pre 𝒯 M ℱ P I E S U A.counit
    module Change = Retargeting.OverBase 𝒯 M ℱ P I E S t q
    module Final = Retargeting.OverBase 𝒯 M ℱ P I E S t t
  module Core = Absolute.Composite 𝒯 M ℱ P I E S Q A.adjunction B′.adjunction
    using (adjunction; counit-comparison; unit-invertible; counit-invertible)

  counit-at : Over.MorphismOver t q (compose-over L (compose-over R U)) U
  counit-at = Change.retarget Pre.value (associator-over U R L) (left-unit-over U)
  module Post = Whiskering.Post 𝒯 M ℱ P I E S K counit-at

  raw-counit : Over.MorphismOver t t (compose-over K (compose-over L (compose-over R U))) (identity-over t)
  raw-counit = Over.compose-over-morphism t t Post.value B′.counit

  framed-counit : Over.MorphismOver t t (compose-over (compose-over K L) (compose-over R U)) (identity-over t)
  framed-counit = Final.retarget raw-counit
    (inverse-iso-over (associator-over (compose-over R U) L K)) (identity-iso-over (identity-over t))

  abstract
    counit-over : Over.IsOver t t (compose-over (compose-over K L) (compose-over R U)) (identity-over t)
      (Adjunction.counit Core.adjunction)
    counit-over = Over.identified-isOver t t
      {u = compose-over (compose-over K L) (compose-over R U)} {v = identity-over t}
      {α = Over.MorphismOver.underlying framed-counit} {β = Adjunction.counit Core.adjunction}
      (expressionIso-inverse Core.counit-comparison)
      (Over.MorphismOver.over-base framed-counit)

    adjunction : RelativeAdjunction p t (compose-over K L) (compose-over R U)
    adjunction = record { adjunction = Core.adjunction ; counit-over-base = counit-over }

    unit-invertible : IsInvertibleExpression AA.unit → IsInvertibleExpression BB.unit →
      IsInvertibleExpression (Adjunction.unit (RelativeAdjunction.adjunction adjunction))
    unit-invertible = Core.unit-invertible

    counit-invertible : IsInvertibleExpression AA.counit → IsInvertibleExpression BB.counit →
      IsInvertibleExpression (Adjunction.counit (RelativeAdjunction.adjunction adjunction))
    counit-invertible = Core.counit-invertible

compose-relative-adjunction : {C D T B : CAT} {p : MAP C B} {q : MAP D B} {t : MAP T B}
  {L : FunctorOver p q} {R : FunctorOver q p} {K : FunctorOver q t} {U : FunctorOver t q} →
  RelativeAdjunction p q L R → RelativeAdjunction q t K U →
  RelativeAdjunction p t (compose-over K L) (compose-over R U)
compose-relative-adjunction = Composite.adjunction
```
