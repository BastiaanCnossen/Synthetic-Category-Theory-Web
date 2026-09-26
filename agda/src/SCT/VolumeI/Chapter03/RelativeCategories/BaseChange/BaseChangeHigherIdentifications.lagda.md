# Base change retains higher triangle comparisons

The chosen base-change action is an actual family of relative
identifications. Its naturality therefore retains the triangle witness
one dimension higher. In particular, transporting the full computation
of a lifted identification gives a full relative comparison after base
change, not only an identification of the underlying functors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChangeHigherIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.IdentificationFamilies 𝒯 M ℱ P using (module Family)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherEncoding 𝒯 M ℱ P using (module Higher)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonLifting 𝒯 M ℱ P using (module Lift)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChangeComparisonFamilies 𝒯 M ℱ P using (module Change)

module Identification {C D S T : CAT} (p : MAP S T)
  {f : MAP C T} {g : MAP D T} (u v : FunctorOver f g) where
  module Changed = Change p u v
    using (first; second; functor; family-triangle; triangle-at; action; comparison; module Encoded)
  module Output = Family (lift-triangle Changed.first) (lift-triangle Changed.second)
    Changed.functor Changed.family-triangle using (naturality)

  opaque
    unfolding Changed.triangle-at
    naturality : {x y : Obj-abs Changed.Encoded.category} (δ : x =₁ y) →
      FunctorOverIso₂ (Changed.action x) (Changed.action y)
    naturality δ = Output.naturality δ

  opaque
    congruence : {Φ Ψ : FunctorOverIso u v} → FunctorOverIso₂ Φ Ψ →
      FunctorOverIso₂ (Changed.comparison Φ) (Changed.comparison Ψ)
    congruence Ξ = naturality (Higher.point-comparison u v Ξ)

  module LiftedFamily {A : CAT}
    (cone : Cone Changed.Encoded.leftMap Changed.Encoded.rightMap A)
    (universal : IsPullback cone) where
    module Input = Lift u v cone universal using (action; lift; encoded-computation)

    opaque
      computation : (Φ : FunctorOverIso u v) →
        FunctorOverIso₂
          (Changed.comparison (Input.action (Input.lift Φ)))
          (Changed.comparison Φ)
      computation Φ = naturality (Input.encoded-computation Φ)
```
