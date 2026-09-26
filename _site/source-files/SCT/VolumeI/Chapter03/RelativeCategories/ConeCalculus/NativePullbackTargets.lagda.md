# Native functors into a pullback target

A functor over `C` into `D ×_S C` is equivalent to a functor into `D`
whose triangle is over `S`. Projection in one direction and pullback
lifting in the other retain the specified triangles. Both inverse
comparisons below are native comparisons over the relevant base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle; module Reflect; module Compare)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (triangle-identification)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Target {X C D S : CAT} (f : MAP C S) (g : MAP D S) (r : MAP X C) where
  projection : MAP (Pullback g f) C
  projection = pullback₂
  π : MAP (Pullback g f) D
  π = pullback₁

  forward : FunctorOver r projection → FunctorOver (f ∘ r) g
  forward u = record { lift = π ∘ FunctorLift.lift u
    ; comparison = (f ◁ FunctorLift.comparison u) ∙
        Cone.match (conePre (FunctorLift.lift u) (pullbackCone g f)) }

  projected : FunctorOver (f ∘ projection) g
  projected = record { lift = π ; comparison = pullbackMatch }

  abstract
    forward-normalization : (u : FunctorOver r projection) →
      FunctorOverIso (forward u) (compose-over projected (postbase f u))
    forward-normalization u = triangle-identification _ _ _
      ((isoComp-assoc-at (f ◁ FunctorLift.comparison u)
        (comp-assoc (FunctorLift.lift u) projection f)
        ((pullbackMatch {f = g} {f} ▷ FunctorLift.lift u) ∙
          (comp-assoc (FunctorLift.lift u) π g) ⁻¹)) ⁻¹)

  cone : FunctorOver (f ∘ r) g → Cone g f X
  cone v = record { left = FunctorLift.lift v ; right = r ; match = FunctorLift.comparison v }

  backward : FunctorOver (f ∘ r) g → FunctorOver r projection
  backward v = lift-triangle (cone v)

  abstract
    forward-backward : (v : FunctorOver (f ∘ r) g) → FunctorOverIso (forward (backward v)) v
    forward-backward v = record { underlying = pullbackLift-β₁ (cone v)
      ; compatible = ConeIso.compatible (pullbackLift-β (cone v)) }

  abstract
    backward-identification : {u v : FunctorOver (f ∘ r) g} → FunctorOverIso u v →
      FunctorOverIso (backward u) (backward v)
    backward-identification {u} {v} Φ = Compare.comparison r (FunctorLift.lift u) (FunctorLift.lift v)
      (FunctorLift.comparison u) (FunctorLift.comparison v) (FunctorOverIso.underlying Φ) (FunctorOverIso.compatible Φ)

  module Recovery (u : FunctorOver r projection) where
    h = FunctorLift.lift u
    θ = FunctorLift.comparison u
    restricted = conePre h (pullbackCone g f)
    normalized : ConeIso restricted (cone (forward u))
    normalized = record { leftIso = idIso (π ∘ h) ; rightIso = θ
      ; compatible = isoComp-unitʳ-at (FunctorLift.comparison (forward u)) ∙
          isoComp-cong (idIso (FunctorLift.comparison (forward u))) (postWhisker-idIso g (π ∘ h)) }
    compared : ConeIso (conePre (FunctorLift.lift (backward (forward u))) (pullbackCone g f)) restricted
    compared = coneIso-compose (coneIso-inverse normalized) (pullbackLift-β (cone (forward u)))

    abstract
      comparison : FunctorOverIso (backward (forward u)) u
      comparison = Reflect.comparison (backward (forward u)) u compared
        (cancel-inverse θ (pullbackLift-β₂ (cone (forward u))))

  module Identification {u v : FunctorOver r projection} (Φ : FunctorOverIso u v) where
    α = FunctorOverIso.underlying Φ
    θu = FunctorLift.comparison u
    θv = FunctorLift.comparison v
    su = conePre (FunctorLift.lift u) (pullbackCone g f)
    sv = conePre (FunctorLift.lift v) (pullbackCone g f)
    square = cone-action (pullbackCone g f) α

    abstract
      comparison : FunctorOverIso (forward u) (forward v)
      comparison = record { underlying = π ◁ α
        ; compatible = isoComp-cong
            ((postWhisker f ◁ FunctorOverIso.compatible Φ) ∙ (postWhisker-isoComp-at f θv (projection ◁ α)) ⁻¹)
            (idIso (Cone.match su)) ∙
          ((isoComp-assoc-at (f ◁ θv) (f ◁ (projection ◁ α)) (Cone.match su)) ⁻¹ ∙
            (isoComp-cong (idIso (f ◁ θv)) (ConeIso.compatible square) ∙
              isoComp-assoc-at (f ◁ θv) (Cone.match sv) (g ◁ (π ◁ α)))) }

abstract
  forward-composite : {X Y C D S : CAT} (f : MAP C S) (g : MAP D S)
    {r : MAP X C} {r′ : MAP Y C} (u : FunctorOver r (pullback₂ {f = g} {f}))
    (v : FunctorOver r′ r) →
    FunctorOverIso (Target.forward f g r′ (compose-over u v))
      (compose-over (Target.forward f g r u) (postbase f v))
  forward-composite f g {r} {r′} u v = compose-iso-over
    (prewhisker-over (postbase f v) (inverse-iso-over (Target.forward-normalization f g r u)))
    (compose-iso-over (inverse-iso-over (associator-over (postbase f v) (postbase f u) (Target.projected f g r)))
      (compose-iso-over (postwhisker-over (Target.projected f g r) (inverse-iso-over (postbase-composite f v u)))
        (Target.forward-normalization f g r′ (compose-over u v))))
```
