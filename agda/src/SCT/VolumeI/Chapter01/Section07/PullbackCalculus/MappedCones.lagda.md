# Mapping a cone by evaluation and currying

The mapped square is obtained by currying the original cone after
evaluation. Its matching is therefore part of the construction. Uncurrying
transfers the pullback lifting and comparison properties to this square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M)
  (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (uncurryCone; uncurryConeIso)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingPre 𝒯 M ℱ using (uncurryCone-restrict)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeCurrying 𝒯 M ℱ using (module CurryCone)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeReflection 𝒯 M ℱ using (module ReflectCone)


module MappedCone {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T : CAT) (s : Cone f g S) where

  module Curried = CurryCone {X = Fun T S} {T = T} {f = f} {g = g}
    (conePre (funEval {T} {S}) s)
  value : Cone (funPost {C = T} f) (funPost g) (Fun T S)
  value = Curried.value

  opaque
    evaluate : {X : CAT} (h : MAP X (Fun T S)) →
      ConeIso (uncurryCone {T = T} {f = f} {g = g} (conePre h value)) (conePre (funUncurry h) s)
    evaluate h = coneIso-compose (conePre-assoc (productMap h (id T)) funEval s)
      (coneIso-compose (coneIso-pre (productMap h (id T)) Curried.comparison)
        (uncurryCone-restrict {f = f} {g = g} h value))

    evaluate-left : {X : CAT} (h : MAP X (Fun T S)) →
      ConeIso.leftIso (evaluate h) =₂ funPost-uncurry (Cone.left s) h
    evaluate-left h = isoComp-cong (idIso (comp-assoc (productMap h (id T)) funEval (Cone.left s)))
      (isoComp-cong (preWhisker (productMap h (id T)) ◁ Curried.comparison-left)
        (idIso (funUncurry-restrict (funPost (Cone.left s)) h)))
    evaluate-right : {X : CAT} (h : MAP X (Fun T S)) →
      ConeIso.rightIso (evaluate h) =₂ funPost-uncurry (Cone.right s) h
    evaluate-right h = isoComp-cong (idIso (comp-assoc (productMap h (id T)) funEval (Cone.right s)))
      (isoComp-cong (preWhisker (productMap h (id T)) ◁ Curried.comparison-right)
        (idIso (funUncurry-restrict (funPost (Cone.right s)) h)))

mappedCone : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T : CAT) → Cone f g S → Cone (funPost {C = T} f) (funPost g) (Fun T S)
mappedCone = MappedCone.value

opaque
  mappedCone-iso : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
    (T : CAT) {s t : Cone f g S} → ConeIso s t → ConeIso (mappedCone T s) (mappedCone T t)
  mappedCone-iso {S = S} {f = f} {g = g} T {s} {t} Φ = ReflectCone.comparison {f = f} {g = g}
    (mappedCone T s) (mappedCone T t)
    (coneIso-compose (coneIso-inverse (MappedCone.Curried.comparison T t))
      (coneIso-compose (coneIso-pre funEval Φ) (MappedCone.Curried.comparison T s)))

opaque
  mappedCone-pre : {C D E S R : CAT} {f : MAP C E} {g : MAP D E}
    (T : CAT) (r : MAP R S) (s : Cone f g S) →
    ConeIso (conePre (funPost r) (mappedCone T s)) (mappedCone T (conePre r s))
  mappedCone-pre {R = R} {f = f} {g = g} T r s = ReflectCone.comparison {f = f} {g = g} 
    (conePre (funPost r) (mappedCone T s)) (mappedCone T (conePre r s))
    (coneIso-compose (coneIso-inverse (MappedCone.Curried.comparison T (conePre r s)))
      (coneIso-compose (coneIso-inverse (conePre-assoc funEval r s))
        (coneIso-compose (cone-action s (funPost-β r)) (MappedCone.evaluate T s (funPost r)))))

```


