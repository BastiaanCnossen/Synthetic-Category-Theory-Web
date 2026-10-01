# Absolute points of relative families

Evaluation at an absolute point retains the triangle over the base. The
comparison uses the defining pullback of the relative functor category,
so it requires neither arrow detection nor functoriality of universals.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Families.AbsolutePointFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamedPointEvaluation 𝒯 M ℱ P
  using (module Named)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingComparisons 𝒯 M ℱ P
  using (module Triangles)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies 𝒯 M ℱ P
  using (point-parameter)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
  using (family; family-composite; curried-beta)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P
  using (module Curry)

abstract
  identify-objects : {C D B : CAT} (p : MAP C B) (q : MAP D B)
    {u v : FunctorOver p q} → FunctorOverIso u v →
    Over.Name.object p q u =₁ Over.Name.object p q v
  identify-objects p q {u} {v} ξ = Over.reflect p q _ _
    (coneIso-compose (coneIso-inverse (Over.Name.comparison p q v))
      (coneIso-compose (Triangles.Identification.cone p q u v ξ)
        (Over.Name.comparison p q u)))

  decoded-point : {C D B : CAT} (p : MAP C B) (q : MAP D B)
    (x : Obj-abs (FunOver p q)) →
    FunctorOverIso (Over.Decode.triangle p q x)
      (PointTriangle (conePre x (pullbackCone (funPost q) (nameFun p))))
  decoded-point p q x = compose-iso-over
    (point-comparison (Over.Decode.cone-comparison p q x))
    (inverse-iso-over (Named.comparison p q (Over.Decode.triangle p q x)))

  decoded-name : {C D B : CAT} (p : MAP C B) (q : MAP D B) (u : FunctorOver p q) →
    FunctorOverIso (Over.Decode.triangle p q (Over.Name.object p q u)) u
  decoded-name p q u = compose-iso-over (Named.comparison p q u)
    (compose-iso-over (point-comparison (Over.Name.comparison p q u))
      (decoded-point p q (Over.Name.object p q u)))

  decode-identification : {C D B : CAT} (p : MAP C B) (q : MAP D B)
    {x y : Obj-abs (FunOver p q)} → x =₁ y →
    FunctorOverIso (Over.Decode.triangle p q x) (Over.Decode.triangle p q y)
  decode-identification p q {x} {y} δ = compose-iso-over (inverse-iso-over (decoded-point p q y))
    (compose-iso-over (point-comparison (cone-action (pullbackCone (funPost q) (nameFun p)) δ))
      (decoded-point p q x))

module Family {X C D B : CAT} (p : MAP C B) (q : MAP D B)
  (F : MAP X (FunOver p q)) (x : Obj-abs X) where
  parameter = point-parameter p x

  abstract
    comparison : FunctorOverIso (Over.Decode.triangle p q (F ∘ x))
      (compose-over (family p q F) parameter)
    comparison = compose-iso-over
      (associator-over (terminal-insertion p) (parameter-over-functor p x) (family p q F))
      (compose-iso-over
        (prewhisker-over (terminal-insertion p) (family-composite p q x F))
        (decoded-point p q (F ∘ x)))

module CurriedFamily {X C D B : CAT} (p : MAP C B) (q : MAP D B)
  (v : FunctorOver (p ∘ pr₂ {C = X}) q) (x : Obj-abs X) where
  module Curried = Curry p q (FunctorLift.lift v) (FunctorLift.comparison v)
  module Evaluated = Family p q Curried.functor x

  abstract
    comparison : FunctorOverIso (Over.Decode.triangle p q (Curried.functor ∘ x))
      (compose-over v Evaluated.parameter)
    comparison = compose-iso-over
      (prewhisker-over Evaluated.parameter (curried-beta p q v)) Evaluated.comparison

    object-comparison : (Curried.functor ∘ x) =₁
      Over.Name.object p q (compose-over v Evaluated.parameter)
    object-comparison = identify-objects p q comparison ∙
      (Over.Decode.object-roundtrip p q (Curried.functor ∘ x)) ⁻¹
```
