# Lifting relative identifications with their full computation rule

A pullback cone presenting the anima of relative identifications gives
a lifting operation. Its computation rule compares both the underlying
identification and the triangle witness. The proof decodes the full
factorization comparison, rather than projecting to its left leg.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; module UniversalCone; pullbackLift-cong; pullbackLift-restrict)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding 𝒯 M ℱ P using (module Encoding)

module Lift {A C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g)
  (cone : Cone (Encoding.leftMap u v) (Encoding.rightMap u v) A)
  (universal : IsPullback cone) where
  module Encoded = Encoding u v
  module Factor = UniversalCone cone universal using (factor; factor-β)

  action : Obj-abs A → FunctorOverIso u v
  action α = Encoded.decode (conePre α cone)

  lift : FunctorOverIso u v → Obj-abs A
  lift Φ = Factor.factor (Encoded.encode Φ)

  comparison-map : MAP A Encoded.category
  comparison-map = pullbackLift cone

  opaque
    point-image : (Φ : FunctorOverIso u v) →
      (comparison-map ∘ lift Φ) =₁ Encoded.point Φ
    point-image Φ = FunctorLift.comparison (equiv-lift universal (Encoded.point Φ))

    action-image : (α : Obj-abs A) →
      (comparison-map ∘ α) =₁ Encoded.point (action α)
    action-image α = pullbackLift-cong (Encoded.Normalize.comparison (conePre α cone)) ∙
      (pullbackLift-restrict α cone) ⁻¹

  opaque
    encoded-computation : (Φ : FunctorOverIso u v) →
      Encoded.point (action (lift Φ)) =₁ Encoded.point Φ
    encoded-computation Φ = point-image Φ ∙ (action-image (lift Φ)) ⁻¹

  opaque
    cone-computation : (Φ : FunctorOverIso u v) →
      ConeIso (conePre (lift Φ) cone) (Encoded.encode Φ)
    cone-computation Φ = Factor.factor-β (Encoded.encode Φ)

  opaque
    computation : (Φ : FunctorOverIso u v) → FunctorOverIso₂ (action (lift Φ)) Φ
    computation Φ = Encoded.decode-into _ Φ (cone-computation Φ)

  record Result (Φ : FunctorOverIso u v) : Set m where
    field
      comparison : Obj-abs A
      full-image : FunctorOverIso₂ (action comparison) Φ
      encoded-image : Encoded.point (action comparison) =₁ Encoded.point Φ

  opaque
    result : (Φ : FunctorOverIso u v) → Result Φ
    result Φ = record { comparison = lift Φ ; full-image = computation Φ
      ; encoded-image = encoded-computation Φ }
```
