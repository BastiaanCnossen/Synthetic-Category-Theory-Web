# Lifting triangles into a pullback

A cone with a specified right leg gives a functor over that leg. A
comparison which fixes the right leg lifts to an identification over the
base. The second projection computation of pullback lifting supplies the
triangle compatibility.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (module Lift)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

lift-triangle : {X C D S : CAT} {g : MAP C S} {p : MAP D S}
  (s : Cone g p X) → FunctorOver (Cone.right s) (pullback₂ {f = g} {p})
lift-triangle s = record { lift = pullbackLift s ; comparison = pullbackLift-β₂ s }

module Compare {X C D S : CAT} {g : MAP C S} {p : MAP D S}
  (r : MAP X D) (h k : MAP X C) (θ : (g ∘ h) =₁ (p ∘ r)) (ψ : (g ∘ k) =₁ (p ∘ r))
  (α : h =₁ k) (χ : (ψ ∙ (g ◁ α)) =₂ θ) where
  s : Cone g p X
  s = record { left = h ; right = r ; match = θ }
  t : Cone g p X
  t = record { left = k ; right = r ; match = ψ }

  cones : ConeIso s t
  cones = record { leftIso = α ; rightIso = idIso r
    ; compatible = isoComp-cong ((postWhisker-idIso p r) ⁻¹) (idIso θ) ∙
        ((isoComp-unitˡ-at θ) ⁻¹ ∙ χ) }
  βs : (pullback₂ ∘ pullbackLift s) =₁ r
  βs = pullbackLift-β₂ s
  βt : (pullback₂ ∘ pullbackLift t) =₁ r
  βt = pullbackLift-β₂ t
  compared : ConeIso (conePre (pullbackLift s) (pullbackCone g p))
    (conePre (pullbackLift t) (pullbackCone g p))
  compared = coneIso-compose (coneIso-inverse (pullbackLift-β t))
    (coneIso-compose cones (pullbackLift-β s))
  module Lifted = Lift (pullbackLift s) (pullbackLift t) compared

  abstract
    comparison : FunctorOverIso (lift-triangle s) (lift-triangle t)
    comparison = record { underlying = Lifted.lift
      ; compatible = isoComp-unitˡ-at βs ∙
          (cancel-inverse βt (idIso r ∙ βs) ∙
            isoComp-cong (idIso βt) Lifted.right-image) }

module Reflect {X C D S : CAT} {g : MAP C S} {p : MAP D S} {r : MAP X D}
  (u v : FunctorOver r (pullback₂ {f = g} {p}))
  (Φ : ConeIso (conePre (FunctorLift.lift u) (pullbackCone g p))
    (conePre (FunctorLift.lift v) (pullbackCone g p)))
  (χ : (FunctorLift.comparison v ∙ ConeIso.rightIso Φ) =₂ FunctorLift.comparison u) where
  private
    module Lifted = Lift (FunctorLift.lift u) (FunctorLift.lift v) Φ
  induced-cone : FunctorLift.lift u =₁ FunctorLift.lift v →
    ConeIso (conePre (FunctorLift.lift u) (pullbackCone g p))
      (conePre (FunctorLift.lift v) (pullbackCone g p))
  induced-cone α = Lifted.Encoding.decode (conePre α Lifted.J.comparisonCone)
  abstract
    comparison : FunctorOverIso u v
    comparison = record { underlying = Lifted.lift
      ; compatible = χ ∙ isoComp-cong (idIso (FunctorLift.comparison v)) Lifted.right-image }

    -- Retain the full cone computation of this particular lift, rather
    -- than only its underlying identification or its second projection.
    cone-computation : ConeIso₂
      (induced-cone (FunctorOverIso.underlying comparison)) Φ
    cone-computation = Lifted.comparison-image

    triangle-computation : FunctorOverIso.compatible comparison =₃
      (χ ∙ isoComp-cong (idIso (FunctorLift.comparison v)) (ConeIso₂.rightId cone-computation))
    triangle-computation = idIso _

module ToCone {X C D S : CAT} {g : MAP C S} {p : MAP D S}
  (s : Cone g p X) (u : FunctorOver (Cone.right s) (pullback₂ {f = g} {p}))
  (Φ : ConeIso (conePre (FunctorLift.lift u) (pullbackCone g p)) s)
  (χ : ConeIso.rightIso Φ =₂ FunctorLift.comparison u) where
  v = lift-triangle s
  compared = coneIso-compose (coneIso-inverse (pullbackLift-β s)) Φ
  abstract
    comparison : FunctorOverIso u v
    comparison = Reflect.comparison u v compared
      (χ ∙ cancel-inverse (pullbackLift-β₂ s) (ConeIso.rightIso Φ))
```
