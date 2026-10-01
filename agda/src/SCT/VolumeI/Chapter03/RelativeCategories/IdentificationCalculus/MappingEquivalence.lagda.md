# The mapping anima of relative identifications

Compare explicit relative identifications with identifications between
the corresponding points of the relative mapping anima. Starting with the pullback
comparison for the named objects, change its endpoints along their
naming comparisons, uncurry, restrict along the terminal insertion,
and use the evaluation comparisons to recover the original endpoints.
Every step is an equivalence of the full comparison animae.

`Naming.underlying-computation` follows the five left projections on
the whole comparison anima. `identify-underlying` and `lift-underlying`
compute the underlying comparisons of the two conversions.

Choose both conversions through this composite equivalence. Its lift
computation and the core-naming roundtrips prove both roundtrip laws.
They also give congruence and reflection for full higher relative
identifications, including the compatibility with the triangle witness.

`NativeNames` exposes these operations at the existing `Over.name-over`
endpoints. These are new conversion choices. Agreement with the older
`Over.identify-cones` and `Over.named-cones-identify` is not asserted.
The fixed-endpoint roundtrips do not establish compatibility of these
conversions with identities, composition, or endpoint changes.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeIdentificationTransport as Transport
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.CoreNamingNaturality as CoreNaming
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.Transport as NativeTransport

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.MappingEquivalence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding 𝒯 M ℱ P using (module Encoding)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherCalculus 𝒯 M ℱ P using (module Calculus)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherEncoding 𝒯 M ℱ P using (module Higher)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ComparisonCospan 𝒯 M ℱ P using (module Uncurrying)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (EvaluatedCone; terminal-insertion)
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamedPointEvaluation as Evaluation

module Naming {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) where
  module U = Over.Name f g u
  module V = Over.Name f g v
  module E = Encoding u v
  module H = Calculus u v using (compose; inverse)
  module HigherInput = Higher u v using (point-comparison)
  module Original = Comparison.IsoComparison 𝒯 dataPullback U.object V.object using (forward; comparisonCone; leftMap; rightMap; Left)
  module Changed = Transport.Transport 𝒯 P U.comparison V.comparison using (pullbackMap; equivalence; left-projection; module Left)
  module Evaluated = Uncurrying U.cone V.cone
    using (cospan; left; left-isEquiv; right-isEquiv; base-isEquiv)
  module Restricted = NativeTransport.Restriction 𝒯 M ℱ P (terminal-insertion f)
    (EvaluatedCone U.cone) (EvaluatedCone V.cone) using (functor; equivalence; cospan; left)
  module Normalized = NativeTransport.Endpoints 𝒯 M ℱ P
    (Evaluation.Named.comparison 𝒯 M ℱ P f g u)
    (Evaluation.Named.comparison 𝒯 M ℱ P f g v) using (functor; equivalence; cospan; module Left)

  cone-comparison = Changed.pullbackMap ∘ Original.forward
  evaluated-comparison = CospanMap.pullbackMap Evaluated.cospan ∘ cone-comparison
  restricted-comparison = Restricted.functor ∘ evaluated-comparison
  comparison : MAP (U.object ＝ V.object) E.category
  comparison = Normalized.functor ∘ restricted-comparison

  opaque
    cone-isEquiv : IsEquiv cone-comparison
    cone-isEquiv = equiv-compose Original.forward Changed.pullbackMap
      (pullback-isoMap-isEquiv U.object V.object) Changed.equivalence
    evaluated-isEquiv : IsEquiv evaluated-comparison
    evaluated-isEquiv = equiv-compose cone-comparison (CospanMap.pullbackMap Evaluated.cospan)
      cone-isEquiv (CospanEquivalence.pullbackMap-isEquiv Evaluated.cospan
        Evaluated.left-isEquiv Evaluated.right-isEquiv Evaluated.base-isEquiv)
    restricted-isEquiv : IsEquiv restricted-comparison
    restricted-isEquiv = equiv-compose evaluated-comparison Restricted.functor evaluated-isEquiv
      (Restricted.equivalence (oneProduct-in-isEquiv C))
    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = equiv-compose restricted-comparison Normalized.functor
      restricted-isEquiv Normalized.equivalence

  -- Track the underlying comparison through the same five equivalences.
  original-left : MAP (U.object ＝ V.object) Original.Left
  original-left = postWhisker (Over.forget f g)
  cone-left : MAP (U.object ＝ V.object) (Cone.left U.cone ＝ Cone.left V.cone)
  cone-left = Changed.Left.forward ∘ original-left
  evaluated-left : MAP (U.object ＝ V.object)
    (FunctorLift.lift (EvaluatedCone U.cone) ＝ FunctorLift.lift (EvaluatedCone V.cone))
  evaluated-left = Evaluated.left ∘ cone-left
  restricted-left : MAP (U.object ＝ V.object)
    (FunctorLift.lift (compose-over (EvaluatedCone U.cone) (terminal-insertion f)) ＝
      FunctorLift.lift (compose-over (EvaluatedCone V.cone) (terminal-insertion f)))
  restricted-left = Restricted.left ∘ evaluated-left
  underlying-action : MAP (U.object ＝ V.object) (FunctorLift.lift u ＝ FunctorLift.lift v)
  underlying-action = Normalized.Left.forward ∘ restricted-left

  private
    opaque
      extend-square : {A B C D E : CAT}
        (previous : MAP A B) (next : MAP B C)
        (before : MAP B D) (after : MAP C E)
        (left : MAP D E) (result : MAP A D) →
        (after ∘ next) =₁ (left ∘ before) →
        (before ∘ previous) =₁ result →
        (after ∘ (next ∘ previous)) =₁ (left ∘ result)
      extend-square previous next before after left result next-square previous-square =
        (left ◁ previous-square) ∙
          (comp-assoc previous before left ∙
            ((next-square ▷ previous) ∙ (comp-assoc previous next after) ⁻¹))

  opaque
    original-projection : (pullback₁ ∘ Original.forward) =₁ original-left
    original-projection = ConeIso.leftIso (pullbackLift-β Original.comparisonCone)

    cone-projection : (pullback₁ ∘ cone-comparison) =₁ cone-left
    cone-projection = extend-square Original.forward Changed.pullbackMap
      pullback₁ pullback₁ Changed.Left.forward original-left
      Changed.left-projection original-projection

    evaluated-projection : (pullback₁ ∘ evaluated-comparison) =₁ evaluated-left
    evaluated-projection = extend-square cone-comparison (CospanMap.pullbackMap Evaluated.cospan)
      pullback₁ pullback₁ Evaluated.left cone-left
      (ConeIso.leftIso (CospanMap.pullbackMap-β Evaluated.cospan)) cone-projection

    restricted-projection : (pullback₁ ∘ restricted-comparison) =₁ restricted-left
    restricted-projection = extend-square evaluated-comparison Restricted.functor
      pullback₁ pullback₁ Restricted.left evaluated-left
      (ConeIso.leftIso (CospanMap.pullbackMap-β Restricted.cospan)) evaluated-projection

    underlying-computation : (pullback₁ ∘ comparison) =₁ underlying-action
    underlying-computation = extend-square restricted-comparison Normalized.functor
      pullback₁ pullback₁ Normalized.Left.forward restricted-left
      (ConeIso.leftIso (CospanMap.pullbackMap-β Normalized.cospan)) restricted-projection

  module Core = CoreNaming.Roundtrip 𝒯 M U.object V.object
    using (included; on-image; congruence; module At)
  Named : Set m
  Named = nameMap U.object =₁ nameMap V.object

  chosen : (Φ : FunctorOverIso u v) → FunctorLift comparison (E.point Φ)
  chosen Φ = equiv-lift comparison-isEquiv (E.point Φ)
  lift : FunctorOverIso u v → U.object =₁ V.object
  lift Φ = FunctorLift.lift (chosen Φ)
  name-native : FunctorOverIso u v → Named
  name-native Φ = nameMapIso (lift Φ)
  identify-native : Named → FunctorOverIso u v
  identify-native α = E.value (comparison ∘ Core.included α)

  opaque
    image : (Φ : FunctorOverIso u v) → (comparison ∘ lift Φ) =₁ E.point Φ
    image Φ = FunctorLift.comparison (chosen Φ)

    identify-underlying : (α : Named) →
      FunctorOverIso.underlying (identify-native α) =₂ (underlying-action ∘ Core.included α)
    identify-underlying α = (underlying-computation ▷ Core.included α) ∙
      (comp-assoc (Core.included α) comparison pullback₁) ⁻¹

    lift-underlying : (Φ : FunctorOverIso u v) →
      (underlying-action ∘ lift Φ) =₂ FunctorOverIso.underlying Φ
    lift-underlying Φ = ConeIso.leftIso (pullbackLift-β (E.encode Φ)) ∙
      ((pullback₁ ◁ image Φ) ∙
        (comp-assoc (lift Φ) comparison pullback₁ ∙ (underlying-computation ▷ lift Φ) ⁻¹))

    value-congruence : {x y : Obj-abs E.category} → x =₁ y →
      FunctorOverIso₂ (E.value x) (E.value y)
    value-congruence {x} {y} δ = E.decode-comparison
      {z = conePre x (pullbackCone E.leftMap E.rightMap)}
      {z′ = conePre y (pullbackCone E.leftMap E.rightMap)}
      (cone-action (pullbackCone E.leftMap E.rightMap) δ)

    identify-congruence : {α β : Named} → α =₂ β →
      FunctorOverIso₂ (identify-native α) (identify-native β)
    identify-congruence {α} {β} δ = value-congruence
      {x = comparison ∘ Core.included α} {y = comparison ∘ Core.included β}
      (comparison ◁ Core.congruence δ)

    native-roundtrip : (Φ : FunctorOverIso u v) →
      FunctorOverIso₂ (identify-native (name-native Φ)) Φ
    native-roundtrip Φ = H.compose
      {Φ = identify-native (name-native Φ)} {Ψ = E.value (E.point Φ)} {Ω = Φ}
      (E.point-computation Φ)
      (value-congruence {x = comparison ∘ Core.included (name-native Φ)} {y = E.point Φ}
        (image Φ ∙ (comparison ◁ Core.on-image (lift Φ))))

    named-roundtrip : (α : Named) → name-native (identify-native α) =₂ α
    named-roundtrip α = Core.At.computation α ∙ nameMap-Iso₂
      (equiv-reflect comparison-isEquiv (lift (identify-native α)) (Core.included α)
        ((E.value-computation (comparison ∘ Core.included α)) ⁻¹ ∙ image (identify-native α)))

    name-congruence : {Φ Ψ : FunctorOverIso u v} → FunctorOverIso₂ Φ Ψ →
      name-native Φ =₂ name-native Ψ
    name-congruence {Φ} {Ψ} Ξ = nameMap-Iso₂
      (equiv-reflect comparison-isEquiv (lift Φ) (lift Ψ)
        ((image Ψ) ⁻¹ ∙ (HigherInput.point-comparison {Φ = Φ} {Ψ = Ψ} Ξ ∙ image Φ)))

    higher-reflection : {Φ Ψ : FunctorOverIso u v} → name-native Φ =₂ name-native Ψ →
      FunctorOverIso₂ Φ Ψ
    higher-reflection {Φ} {Ψ} δ = H.compose
      {Φ = Φ} {Ψ = identify-native (name-native Ψ)} {Ω = Ψ} (native-roundtrip Ψ)
      (H.compose {Φ = Φ} {Ψ = identify-native (name-native Φ)} {Ω = identify-native (name-native Ψ)}
        (identify-congruence {α = name-native Φ} {β = name-native Ψ} δ)
        (H.inverse {Φ = identify-native (name-native Φ)} {Ψ = Φ} (native-roundtrip Φ)))

module NativeNames {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) where
  module Correspondence = Naming u v
    using (name-native; identify-native; named-roundtrip; native-roundtrip; name-congruence;
      identify-congruence; higher-reflection)

  opaque
    unfolding Over.name-over
    encode : FunctorOverIso u v → Over.name-over f g u =₁ Over.name-over f g v
    encode = Correspondence.name-native
    decode : Over.name-over f g u =₁ Over.name-over f g v → FunctorOverIso u v
    decode = Correspondence.identify-native
    roundtrip : (α : Over.name-over f g u =₁ Over.name-over f g v) → encode (decode α) =₂ α
    roundtrip = Correspondence.named-roundtrip
    native-roundtrip : (Φ : FunctorOverIso u v) → FunctorOverIso₂ (decode (encode Φ)) Φ
    native-roundtrip = Correspondence.native-roundtrip
    decode-congruence : {α β : Over.name-over f g u =₁ Over.name-over f g v} → α =₂ β →
      FunctorOverIso₂ (decode α) (decode β)
    decode-congruence {α} {β} = Correspondence.identify-congruence {α = α} {β = β}
    congruence : {Φ Ψ : FunctorOverIso u v} → FunctorOverIso₂ Φ Ψ → encode Φ =₂ encode Ψ
    congruence {Φ} {Ψ} = Correspondence.name-congruence {Φ = Φ} {Ψ = Ψ}
    reflection : {Φ Ψ : FunctorOverIso u v} → encode Φ =₂ encode Ψ → FunctorOverIso₂ Φ Ψ
    reflection {Φ} {Ψ} = Correspondence.higher-reflection {Φ = Φ} {Ψ = Ψ}
```
