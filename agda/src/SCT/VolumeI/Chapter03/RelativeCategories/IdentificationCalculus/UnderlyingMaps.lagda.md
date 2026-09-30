# The underlying comparison of relative naming

The common comparison equivalence first transports the named endpoints,
then uncurries, restricts along the terminal insertion, and transports
the evaluated endpoints back. `Underlying.computation` writes its left
projection in exactly this form. The decoder and lift inherit the two
pointwise computations `identify-computation` and `lift-computation`.

`named-included` compares the transported named left leg with the left
leg of the existing `Over.identify-cones`. Consequently, `decoded-old-cone`
expresses the new decoder's underlying comparison by uncurrying that
existing left leg and changing the evaluated endpoints.

This compares underlying identifications only. It does not identify
the full triangle witnesses or the new decoder with the old native
reflector.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeIdentificationTransport as Transport
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.MappingEquivalence as Naming
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamedPointEvaluation as Evaluation

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.UnderlyingMaps
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
  using (funUncurryIso; funUncurry-isoMap; uncurryFamily-at)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (coreInclusion)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M using (coreInclusion-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (EvaluatedCone)

module Conjugate {X Y : CAT} {x x′ y y′ : MAP X Y}
  (α : x =₁ x′) (β : y =₁ y′) where
  module K = Transport.Conjugation 𝒯 P α β using (forward; evaluate)
  opaque
    at : (γ : x =₁ y) → (K.forward ∘ γ) =₂ (β ∙ (γ ∙ α ⁻¹))
    at γ = isoComp-cong (const-One β)
      (isoComp-cong (idIso γ) (const-One (α ⁻¹))) ∙ K.evaluate γ

module Pasting {X Y : CAT} {a b c d e f : MAP X Y}
  (α₁ : a =₁ b) (α₂ : b =₁ c) (β₁ : d =₁ e) (β₂ : e =₁ f) (γ : a =₁ d) where
  opaque
    comparison : (β₂ ∙ ((β₁ ∙ (γ ∙ α₁ ⁻¹)) ∙ α₂ ⁻¹)) =₂
      ((β₂ ∙ β₁) ∙ (γ ∙ (α₂ ∙ α₁) ⁻¹))
    comparison = (isoComp-assoc-at β₂ β₁ (γ ∙ (α₂ ∙ α₁) ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso β₂)
        (isoComp-cong (idIso β₁)
          (isoComp-cong (idIso γ) ((inverse-composite α₂ α₁) ⁻¹) ∙
            isoComp-assoc-at γ (α₁ ⁻¹) (α₂ ⁻¹)) ∙
          isoComp-assoc-at β₁ (γ ∙ α₁ ⁻¹) (α₂ ⁻¹))

module PostConjugate {X Y Z : CAT} (F : MAP Y Z)
  {x x′ y y′ : MAP X Y} (α : x =₁ x′) (β : y =₁ y′) (γ : x =₁ y) where
  opaque
    comparison : (F ◁ (β ∙ (γ ∙ α ⁻¹))) =₂ ((F ◁ β) ∙ ((F ◁ γ) ∙ (F ◁ α) ⁻¹))
    comparison = isoComp-cong (idIso (F ◁ β))
      (isoComp-cong (idIso (F ◁ γ)) (post-inverse F α) ∙
        postWhisker-isoComp-at F γ (α ⁻¹)) ∙
      postWhisker-isoComp-at F β (γ ∙ α ⁻¹)

module Underlying {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) where
  module N = Naming.Naming 𝒯 M ℱ P u v
  h = FunctorLift.lift u
  k = FunctorLift.lift v
  βu = ConeIso.leftIso N.U.comparison
  βv = ConeIso.leftIso N.V.comparison
  δu = FunctorOverIso.underlying (Evaluation.Named.comparison 𝒯 M ℱ P f g u)
  δv = FunctorOverIso.underlying (Evaluation.Named.comparison 𝒯 M ℱ P f g v)

  named : N.U.object =₁ N.V.object → Cone.left N.U.cone =₁ Cone.left N.V.cone
  named γ = βv ∙ ((Over.forget f g ◁ γ) ∙ βu ⁻¹)

  evaluated : N.U.object =₁ N.V.object →
    FunctorLift.lift (EvaluatedCone N.U.cone) =₁
    FunctorLift.lift (EvaluatedCone N.V.cone)
  evaluated γ = funUncurryIso (named γ)

  value : N.U.object =₁ N.V.object → h =₁ k
  value γ = δv ∙ ((evaluated γ ▷ oneProduct-in C) ∙ δu ⁻¹)

  opaque
    named-computation : (γ : N.U.object =₁ N.V.object) → (N.cone-left ∘ γ) =₂ named γ
    named-computation γ = Conjugate.at βu βv (Over.forget f g ◁ γ) ∙
      comp-assoc γ N.original-left N.Changed.Left.forward

    uncurrying-left : N.Evaluated.left =₁ funUncurry-isoMap (Cone.left N.U.cone) (Cone.left N.V.cone)
    uncurrying-left = comp-unitʳ (funUncurry-isoMap (Cone.left N.U.cone) (Cone.left N.V.cone)) ∙
      (uncurryFamily-at (id (Cone.left N.U.cone ＝ Cone.left N.V.cone))) ⁻¹

    evaluated-computation : (γ : N.U.object =₁ N.V.object) → (N.evaluated-left ∘ γ) =₂ evaluated γ
    evaluated-computation γ =
      (funUncurry-isoMap (Cone.left N.U.cone) (Cone.left N.V.cone) ◁ named-computation γ) ∙
      ((uncurrying-left ▷ (N.cone-left ∘ γ)) ∙ comp-assoc γ N.cone-left N.Evaluated.left)

    restricted-computation : (γ : N.U.object =₁ N.V.object) →
      (N.restricted-left ∘ γ) =₂ (evaluated γ ▷ oneProduct-in C)
    restricted-computation γ = (preWhisker (oneProduct-in C) ◁ evaluated-computation γ) ∙
      comp-assoc γ N.evaluated-left N.Restricted.left

    computation : (γ : N.U.object =₁ N.V.object) → (N.underlying-action ∘ γ) =₂ value γ
    computation γ =
      isoComp-cong (idIso δv) (isoComp-cong (restricted-computation γ) (idIso (δu ⁻¹))) ∙
      (Conjugate.at δu δv (N.restricted-left ∘ γ) ∙
        comp-assoc γ N.restricted-left N.Normalized.Left.forward)

    identify-computation : (α : N.Named) →
      FunctorOverIso.underlying (N.identify-native α) =₂ value (N.Core.included α)
    identify-computation α = computation (N.Core.included α) ∙ N.identify-underlying α

    lift-computation : (Φ : FunctorOverIso u v) → value (N.lift Φ) =₂ FunctorOverIso.underlying Φ
    lift-computation Φ = N.lift-underlying Φ ∙ (computation (N.lift Φ)) ⁻¹

  opaque
    unfolding Over.name-over
    included : Over.name-over f g u =₁ Over.name-over f g v → N.U.object =₁ N.V.object
    included = N.Core.included

  opaque
    unfolding Over.name-over Over.named-cone Over.identify-cones included
    named-included : (α : Over.name-over f g u =₁ Over.name-over f g v) → named (included α) =₂
      ConeIso.leftIso (Over.identify-cones f g u v α)
    named-included α =
      Pasting.comparison (Over.forget f g ◁ coreInclusion-name N.U.object) βu
        (Over.forget f g ◁ coreInclusion-name N.V.object) βv
        (Over.forget f g ◁ (coreInclusion (FunOver f g) ◁ α)) ∙
      isoComp-cong (idIso βv)
        (isoComp-cong
          (PostConjugate.comparison (Over.forget f g)
            (coreInclusion-name N.U.object) (coreInclusion-name N.V.object)
            (coreInclusion (FunOver f g) ◁ α)) (idIso (βu ⁻¹)))

  module Names = Naming.NativeNames 𝒯 M ℱ P u v using (decode)

  opaque
    unfolding Over.name-over included Names.decode
    decoded-old-cone : (α : Over.name-over f g u =₁ Over.name-over f g v) →
      FunctorOverIso.underlying (Names.decode α) =₂
        (δv ∙ ((funUncurryIso (ConeIso.leftIso (Over.identify-cones f g u v α)) ▷ oneProduct-in C) ∙ δu ⁻¹))
    decoded-old-cone α = isoComp-cong (idIso δv)
      (isoComp-cong
        (preWhisker (oneProduct-in C) ◁
          (funUncurry-isoMap (Cone.left N.U.cone) (Cone.left N.V.cone) ◁ named-included α))
        (idIso (δu ⁻¹))) ∙ identify-computation α
```
