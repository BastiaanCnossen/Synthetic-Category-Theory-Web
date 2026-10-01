# Fibrations from one variable endpoint

A category of arrows with one endpoint given by a functor and the other
fixed is an ordinary relative slice. Pullback nesting compares their
chosen presentations over the variable endpoint parameter.

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

import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointProjectionFibrations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section03.SliceFibrations 𝒯 M ℱ P I E S Q
open import SCT.VolumeI.Chapter04.Section02.BaseChange 𝒯 M ℱ P I
  using (left-base-change; right-base-change)
open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I
  using (module Evaluation)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone)
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (pullbackCone-isPullback; IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)

module Slice {C D : CAT} (f : MAP C D) (d : Obj-abs D) where
  module Source = EndpointFiber f (const d) using (category; base)
  boundary = pair (id D) (const d)
  module Target = EndpointFiber (id D) (const d) using (base)
  source-cone = coneSwap (pullbackCone endpoints (pair f (const d)))
  target-cone = coneSwap (pullbackCone endpoints boundary)

  abstract
    target-isPullback : IsPullback target-cone
    target-isPullback = pullback-swap (pullbackCone endpoints boundary)
      (pullbackCone-isPullback endpoints boundary)

  boundary-frame : (boundary ∘ f) =₁ pair f (const d)
  boundary-frame = pair-cong (comp-unitˡ f) (const-pre d f) ∙ pair-pre (id D) (const d) f
  changed = changeLeft (boundary-frame ⁻¹) source-cone

  abstract
    changed-isPullback : IsPullback changed
    changed-isPullback = ChangeLeft.preserve (boundary-frame ⁻¹) endpoints source-cone
      (pullback-swap (pullbackCone endpoints (pair f (const d)))
        (pullbackCone-isPullback endpoints (pair f (const d))))

  module Universal = UniversalCone target-cone target-isPullback using (factor; factor-β)
  inner-cone = compositeCone f boundary changed
  module Cancel = Cancellation.At 𝒯 P f boundary endpoints target-cone target-isPullback
    changed changed-isPullback (Universal.factor inner-cone) (Universal.factor-β inner-cone)
    using (square; square-isPullback)

  abstract
    projection-isRightFibration : IsEquiv (Evaluation.directed-ev₁ Source.base)
    projection-isRightFibration = right-base-change (coneSwap Cancel.square)
      (pullback-swap Cancel.square Cancel.square-isPullback) (slice-isRightFibration d)

module Coslice {C D : CAT} (f : MAP C D) (d : Obj-abs D) where
  module Source = EndpointFiber (const d) f using (category; base)
  boundary = pair (const d) (id D)
  module Target = EndpointFiber (const d) (id D) using (base)
  source-cone = coneSwap (pullbackCone endpoints (pair (const d) f))
  target-cone = coneSwap (pullbackCone endpoints boundary)

  abstract
    target-isPullback : IsPullback target-cone
    target-isPullback = pullback-swap (pullbackCone endpoints boundary)
      (pullbackCone-isPullback endpoints boundary)

  boundary-frame : (boundary ∘ f) =₁ pair (const d) f
  boundary-frame = pair-cong (const-pre d f) (comp-unitˡ f) ∙ pair-pre (const d) (id D) f
  changed = changeLeft (boundary-frame ⁻¹) source-cone

  abstract
    changed-isPullback : IsPullback changed
    changed-isPullback = ChangeLeft.preserve (boundary-frame ⁻¹) endpoints source-cone
      (pullback-swap (pullbackCone endpoints (pair (const d) f))
        (pullbackCone-isPullback endpoints (pair (const d) f)))

  module Universal = UniversalCone target-cone target-isPullback using (factor; factor-β)
  inner-cone = compositeCone f boundary changed
  module Cancel = Cancellation.At 𝒯 P f boundary endpoints target-cone target-isPullback
    changed changed-isPullback (Universal.factor inner-cone) (Universal.factor-β inner-cone)
    using (square; square-isPullback)

  abstract
    projection-isLeftFibration : IsEquiv (Evaluation.directed-ev₀ Source.base)
    projection-isLeftFibration = left-base-change (coneSwap Cancel.square)
      (pullback-swap Cancel.square Cancel.square-isPullback) (coslice-isLeftFibration d)

```
