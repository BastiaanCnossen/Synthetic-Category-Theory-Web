# Detecting pullbacks after terminal-domain evaluation

Evaluation `Fun One C → C` is an equivalence. Thus converting restriction
cones into endpoint cones reflects their universal property. The conversion
and its compatibility with restriction are already available from Chapter 2;
here we reflect comparisons through evaluation, retaining their matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section01.Lifting.EndpointPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.EndpointRestrictionCones 𝒯 M ℱ P
  using (module Endpoints)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P
  using (cone-isPullback-from-lifting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (reflect-transport-square)
open Pullbacks.PullbackStructure P

module At (C : CAT) where
  open Endpoints C

  reflect-comparison : {Γ A B : CAT} {u : Obj-abs A} {v : Obj-abs B}
    (s t : Cone (funPre {D = C} u) (funPre v) Γ) →
    ConeIso (convert s) (convert t) → ConeIso s t
  reflect-comparison {u = u} {v} s t Φ = record
    { leftIso = α ; rightIso = β
    ; compatible = equiv-reflect (postWhisker-isEquiv e (evaluate-point-isEquiv C) _ _) _ _
        ((postWhisker-isoComp-at e (funPre v ◁ β) (Cone.match s)) ⁻¹ ∙
          (reflected ∙ postWhisker-isoComp-at e (Cone.match t) (funPre u ◁ α))) }
    where
    α = ConeIso.leftIso Φ
    β = ConeIso.rightIso Φ
    reflected = reflect-transport-square
      (component u (Cone.left s)) (component u (Cone.left t))
      (component v (Cone.right s)) (component v (Cone.right t))
      (e ◁ Cone.match s) (e ◁ Cone.match t)
      (e ◁ (funPre u ◁ α)) (e ◁ (funPre v ◁ β))
      (evaluate u ◁ α) (evaluate v ◁ β)
      (component-natural u α) (component-natural v β) (ConeIso.compatible Φ)

  module Detect {Γ A B : CAT} {u : Obj-abs A} {v : Obj-abs B}
    (s : Cone (funPre {D = C} u) (funPre v) Γ) (es : IsPullback (convert s)) where
    module U = UniversalCone (convert s) es

    inverse = U.factor (convert (pullbackCone (funPre u) (funPre v)))

    computation : ConeIso (conePre inverse s) (pullbackCone (funPre u) (funPre v))
    computation = reflect-comparison _ _ (coneIso-compose
      (U.factor-β (convert (pullbackCone (funPre u) (funPre v))))
      (Parameter.comparison inverse s))

    reflect : (h k : MAP Γ Γ) → ConeIso (conePre h s) (conePre k s) → h =₁ k
    reflect h k Φ = U.reflect h k (coneIso-compose (Parameter.comparison k s)
      (coneIso-compose (convertIso Φ) (coneIso-inverse (Parameter.comparison h s))))

    isPullback : IsPullback s
    isPullback = cone-isPullback-from-lifting s inverse computation reflect

  conversion-reflects-pullback : {Γ A B : CAT} {u : Obj-abs A} {v : Obj-abs B}
    (s : Cone (funPre {D = C} u) (funPre v) Γ) → IsPullback (convert s) → IsPullback s
  conversion-reflects-pullback = Detect.isPullback
```
