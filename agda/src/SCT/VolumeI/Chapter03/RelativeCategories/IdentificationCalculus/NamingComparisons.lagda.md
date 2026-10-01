# Naming identifications over a base

An identification of functors over a base includes its compatibility with
the two specified triangles. Naming carries precisely this compatibility
to an identification in the relative mapping anima.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingLaws as Naming
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.EquivalenceReflectionComputation as ReflectionComputation

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ using (post-nameFun)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications 𝒯 M ℱ
open Naming 𝒯 M ℱ using (nameFunIso-comp)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.FixedBoundaryComparisons 𝒯 M
  using (module FixedRight; module Normalize)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; left-evaluate; right-evaluate)

module Triangles {C D S : CAT} (f : MAP C S) (g : MAP D S) where
  open Over f g

  abstract
    triangleNameMap-at : (h : MAP C D) (θ : (g ∘ h) =₁ f) →
      (triangleNameMap h ∘ θ) =₂
        ((comp-unitʳ (nameFun f)) ⁻¹ ∙ (nameFunIso θ ∙ post-nameFun g h))
    triangleNameMap-at h θ =
      isoComp-cong (const-One ((comp-unitʳ (nameFun f)) ⁻¹))
        (isoComp-cong (idIso (nameFunIso θ)) (const-One (post-nameFun g h))) ∙
      (left-evaluate ((comp-unitʳ (nameFun f)) ⁻¹) (nameFunIso θ ∙ const (post-nameFun g h)) ∙
        ((leftMultiply ((comp-unitʳ (nameFun f)) ⁻¹) ◁ right-evaluate (post-nameFun g h) (nameFunIso θ)) ∙
          ((leftMultiply ((comp-unitʳ (nameFun f)) ⁻¹) ◁
              comp-assoc θ (nameFun-isoMap (g ∘ h) f) (rightMultiply (post-nameFun g h))) ∙
            comp-assoc θ (rightMultiply (post-nameFun g h) ∘ nameFun-isoMap (g ∘ h) f)
              (leftMultiply ((comp-unitʳ (nameFun f)) ⁻¹)))))

  module Action {h k : MAP C D} (α : h =₁ k) (θ : (g ∘ k) =₁ f) where
    unit : nameFun f =₁ (nameFun f ∘ id One)
    unit = (comp-unitʳ (nameFun f)) ⁻¹
    named : nameFun h =₁ nameFun k
    named = nameFunIso α
    ν : (funPost g ∘ nameFun h) =₁ (funPost g ∘ nameFun k)
    ν = funPost g ◁ named

    abstract
      comparison : ((triangleNameMap k ∘ θ) ∙ ν) =₂
        (triangleNameMap h ∘ (θ ∙ (g ◁ α)))
      comparison = (triangleNameMap-at h (θ ∙ (g ◁ α))) ⁻¹ ∙
        (isoComp-cong (idIso unit)
          (isoComp-cong ((nameFunIso-comp θ (g ◁ α)) ⁻¹) (idIso (post-nameFun g h)) ∙
            ((isoComp-assoc-at (nameFunIso θ) (nameFunIso (g ◁ α)) (post-nameFun g h)) ⁻¹ ∙
              (isoComp-cong (idIso (nameFunIso θ)) (Naming.Post.natural 𝒯 M ℱ g α) ∙
                isoComp-assoc-at (nameFunIso θ) (post-nameFun g k) ν))) ∙
          (isoComp-assoc-at unit (nameFunIso θ ∙ post-nameFun g k) ν ∙
            isoComp-cong (triangleNameMap-at k θ) (idIso ν)))

  module Identification (u v : FunctorOver f g) (Φ : FunctorOverIso u v) where
    open FunctorOverIso Φ
    hu : MAP C D
    hu = FunctorLift.lift u
    hv : MAP C D
    hv = FunctorLift.lift v
    θu : (g ∘ hu) =₁ f
    θu = FunctorLift.comparison u
    θv : (g ∘ hv) =₁ f
    θv = FunctorLift.comparison v

    opaque
      matching-comparison : ((triangleNameMap hv ∘ θv) ∙ (funPost g ◁ nameFunIso underlying)) =₂
        (triangleNameMap hu ∘ θu)
      matching-comparison = (triangleNameMap hu ◁ compatible) ∙ Action.comparison underlying θv

      cone : ConeIso (Name.cone u) (Name.cone v)
      cone = record
        { leftIso = nameFunIso underlying
        ; rightIso = idIso (id One)
        ; compatible =
            isoComp-cong ((postWhisker-idIso (nameFun f) (id One)) ⁻¹)
              (idIso (triangleNameMap hu ∘ θu)) ∙
            ((isoComp-unitˡ-at (triangleNameMap hu ∘ θu)) ⁻¹ ∙ matching-comparison) }

      identification : name-over u =₁ name-over v
      identification = named-cones-identify u v cone
  module Reflection (u v : FunctorOver f g) (Φ : ConeIso (Name.cone u) (Name.cone v)) where
    hu : MAP C D
    hu = FunctorLift.lift u
    hv : MAP C D
    hv = FunctorLift.lift v
    θu : (g ∘ hu) =₁ f
    θu = FunctorLift.comparison u
    θv : (g ∘ hv) =₁ f
    θv = FunctorLift.comparison v
    opaque
      chosen : FunctorLift (nameFun-isoMap hu hv) (ConeIso.leftIso Φ)
      chosen = equiv-lift (nameFun-isoMap-isEquiv hu hv) (ConeIso.leftIso Φ)
    α : hu =₁ hv
    α = FunctorLift.lift chosen

    opaque
      right-comparison : ConeIso.rightIso Φ =₂ idIso (id One)
      right-comparison = equiv-reflect (terminalIso-isEquiv (id One) (id One)) _ _
        (terminal-iso _ _)

      matching-comparison : ((triangleNameMap hv ∘ θv) ∙ (funPost g ◁ nameFunIso α)) =₂
        (triangleNameMap hu ∘ θu)
      matching-comparison = isoComp-unitˡ-at (triangleNameMap hu ∘ θu) ∙
        (isoComp-cong (postWhisker-idIso (nameFun f) (id One) ∙
            (postWhisker (nameFun f) ◁ right-comparison))
          (idIso (triangleNameMap hu ∘ θu)) ∙
          (ConeIso.compatible Φ ∙
            isoComp-cong (idIso (triangleNameMap hv ∘ θv))
              (postWhisker (funPost g) ◁ FunctorLift.comparison chosen)))

    opaque
      triangle-witness : (θv ∙ (g ◁ α)) =₂ θu
      triangle-witness = equiv-reflect (triangleNameMap-isEquiv hu) _ _
        (matching-comparison ∙ (Action.comparison α θv) ⁻¹)

    over : FunctorOverIso u v
    over = record
      { underlying = α
      ; compatible = triangle-witness }

    opaque
      unfolding triangle-witness Identification.matching-comparison
      underlying-image : nameFunIso (FunctorOverIso.underlying over) =₂ ConeIso.leftIso Φ
      underlying-image = FunctorLift.comparison chosen

      triangle-image : (triangleNameMap hu ◁ FunctorOverIso.compatible over) =₃
        (matching-comparison ∙ (Action.comparison α θv) ⁻¹)
      triangle-image = ReflectionComputation.Reflection.computation 𝒯 M
        (triangleNameMap-isEquiv hu) _ _
        (matching-comparison ∙ (Action.comparison α θv) ⁻¹)

      matching-image : Identification.matching-comparison u v over =₃ matching-comparison
      matching-image = isoComp-unitʳ-at matching-comparison ∙
        (isoComp-cong (idIso matching-comparison) (isoComp-inverseˡ-at (Action.comparison α θv)) ∙
        (isoComp-assoc-at matching-comparison ((Action.comparison α θv) ⁻¹) (Action.comparison α θv) ∙
          isoComp-cong triangle-image (idIso (Action.comparison α θv))))

    module Roundtrip where
      module Encoded = Identification u v over using (cone; matching-comparison)
      b = triangleNameMap hu ∘ θu
      module Right = FixedRight {h = nameFun f ∘ id One} b
        using (action; congruence; composite; inverse)
      q = postWhisker (nameFun f) ◁ right-comparison
      unit = postWhisker-idIso (nameFun f) (id One)
      left = FunctorLift.comparison chosen
      right = right-comparison ⁻¹
      left-boundary = isoComp-cong (idIso (triangleNameMap hv ∘ θv))
        (postWhisker (funPost g) ◁ left)
      base = ConeIso.compatible Φ ∙ left-boundary
      encoded = Right.action (unit ⁻¹) ∙
        ((isoComp-unitˡ-at b) ⁻¹ ∙ Encoded.matching-comparison)
      right-boundary = Right.action (postWhisker (nameFun f) ◁ right)

      opaque
        unfolding matching-comparison
        normalization-image : Encoded.matching-comparison =₃
          (isoComp-unitˡ-at b ∙ (Right.action (unit ∙ q) ∙ base))
        normalization-image = matching-image

      module Normalized = Normalize.At b q unit base Encoded.matching-comparison normalization-image
        using (square)

      opaque
        right-image : right-boundary =₃ Right.action (q ⁻¹)
        right-image = Right.congruence (post-inverse (postWhisker (nameFun f)) right-comparison)

        square : base =₃ (right-boundary ∙ encoded)
        square = isoComp-cong (right-image ⁻¹) (idIso encoded) ∙ Normalized.square

      opaque
        unfolding Identification.cone
        comparison : ConeIso₂ Encoded.cone Φ
        comparison = record { leftId = left ; rightId = right ; compatible = square }

  abstract
    identify-native : (u v : FunctorOver f g) →
      name-over u =₁ name-over v → FunctorOverIso u v
    identify-native u v α = Reflection.over u v (identify-cones u v α)

    decode-name-native : (u : FunctorOver f g) →
      FunctorOverIso (decode-over (name-over u)) u
    decode-name-native u = Reflection.over (decode-over (name-over u)) u (decode-name-cone u)

    decode-native-identification : {x y : Obj-abs (MapOver f g)} →
      x =₁ y → FunctorOverIso (decode-over x) (decode-over y)
    decode-native-identification {x} {y} α =
      Reflection.over (decode-over x) (decode-over y) (decode-identification-cone α)
```

