# Point evaluation of relative families

Decoding a relative mapping point agrees, over the base, with evaluating
its whole pullback cone. Consequently a curried family computes at a
point as its original family restricted to that point, retaining the
specified triangle throughout.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M using (mapPost)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; conePre-assoc)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M using (Core; coreInclusion; coreInclusion-natural)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamedPointEvaluation 𝒯 M ℱ P using (module Named)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (module CurriedTriangle)

abstract
  decoded-point : {C D S : CAT} (f : MAP C S) (g : MAP D S)
    (x : Obj-abs (MapOver f g)) →
    FunctorOverIso (Over.decode-over f g x)
      (PointTriangle (conePre (coreInclusion (FunOver f g) ∘ x) (pullbackCone (funPost g) (nameFun f))))
  decoded-point f g x = compose-iso-over (point-comparison (Over.decoded-cone f g x))
    (inverse-iso-over (Named.comparison f g (Over.decode-over f g x)))

point-parameter : {X C S : CAT} (f : MAP C S) (x : Obj-abs X) →
  FunctorOver f (f ∘ pr₂ {C = X})
point-parameter f x = compose-over (parameter-over-functor f x) (terminal-insertion f)

abstract
  universal-point : {C D S : CAT} (f : MAP C S) (g : MAP D S)
    (x : Obj-abs (MapOver f g)) →
    FunctorOverIso (Over.decode-over f g x)
      (compose-over (EvaluatedCone (pullbackCone (funPost g) (nameFun f)))
        (point-parameter f (coreInclusion (FunOver f g) ∘ x)))
  universal-point f g x = compose-iso-over
    (associator-over (terminal-insertion f)
      (parameter-over-functor f (coreInclusion (FunOver f g) ∘ x))
      (EvaluatedCone (pullbackCone (funPost g) (nameFun f))))
    (compose-iso-over
      (prewhisker-over (terminal-insertion f)
        (evaluated-restriction (coreInclusion (FunOver f g) ∘ x) (pullbackCone (funPost g) (nameFun f))))
      (decoded-point f g x))

module Family {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (F : MAP X (FunOver f g)) (x : Obj-abs (Core X)) where
  object : Obj-abs X
  object = coreInclusion X ∘ x
  cone : Cone (funPost g) (nameFun f) X
  cone = conePre F (pullbackCone (funPost g) (nameFun f))
  parameter : FunctorOver f (f ∘ pr₂ {C = X})
  parameter = point-parameter f object

  abstract
    cores : (coreInclusion (FunOver f g) ∘ (mapPost F ∘ x)) =₁ (F ∘ object)
    cores = comp-assoc x (coreInclusion X) F ∙
      ((coreInclusion-natural F ▷ x) ∙ (comp-assoc x (mapPost F) (coreInclusion (FunOver f g))) ⁻¹)

    cones : ConeIso
      (conePre (coreInclusion (FunOver f g) ∘ (mapPost F ∘ x)) (pullbackCone (funPost g) (nameFun f)))
      (conePre object cone)
    cones = coneIso-compose (coneIso-inverse (conePre-assoc object F (pullbackCone (funPost g) (nameFun f))))
      (cone-action (pullbackCone (funPost g) (nameFun f)) cores)

    comparison : FunctorOverIso (Over.decode-over f g (mapPost F ∘ x))
      (compose-over (EvaluatedCone cone) parameter)
    comparison = compose-iso-over
      (associator-over (terminal-insertion f) (parameter-over-functor f object) (EvaluatedCone cone))
      (compose-iso-over (prewhisker-over (terminal-insertion f) (evaluated-restriction object cone))
        (compose-iso-over (point-comparison cones) (decoded-point f g (mapPost F ∘ x))))

module CurriedFamily {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (v : FunctorOver (f ∘ pr₂ {C = X}) g) (x : Obj-abs (Core X)) where
  module Curried = Curry f g (FunctorLift.lift v) (FunctorLift.comparison v)
  module Local = CurriedTriangle f g (FunctorLift.lift v) (FunctorLift.comparison v)
  module Evaluated = Family f g Curried.functor x

  abstract
    local-comparison : FunctorOverIso (EvaluatedCone Evaluated.cone) v
    local-comparison = record
      { underlying = Local.evaluation-with-image ; compatible = Local.native-beta }

    comparison : FunctorOverIso (Over.decode-over f g (mapPost Curried.functor ∘ x))
      (compose-over v Evaluated.parameter)
    comparison = compose-iso-over (prewhisker-over Evaluated.parameter local-comparison) Evaluated.comparison
```
