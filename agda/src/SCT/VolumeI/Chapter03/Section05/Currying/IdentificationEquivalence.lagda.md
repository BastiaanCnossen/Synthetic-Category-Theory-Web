# Relative currying with computed identification roundtrips

Keep the existing transposed and evaluated objects, the specified
uncurrying functor, and its comparison on named objects. Choose native
factorization and reflection comparisons through `ComputedRelativeNaming`.
`Factor.computation` computes the named factorization comparison.

For identifications, apply uncurrying to their names and conjugate by
the named object comparisons. Decoding defines `At.evaluate-identification`.
The naming roundtrips and the equivalence-reflector computation give
both full native roundtrips: `At.Image.computation` and
`At.Roundtrip.computation`. Congruence and higher reflection retain the
compatibility with the triangle over the base.

This transported action is a new choice. Agreement with native
base-change followed by postwhiskering, composition and restriction
laws for this action, and the pullback-preservation theorem remain
separate obligations. The older native reflector and pullback matching
are unchanged.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingCancellation
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.EquivalenceReflectionComputation as Computation
import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying as Existing
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.MappingEquivalence as Naming

module SCT.VolumeI.Chapter03.Section05.Currying.IdentificationEquivalence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherCalculus 𝒯 M ℱ P using (module Calculus)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open Pullbacks.PullbackStructure P using (pullback₂)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeTransposition 𝒯 M ℱ P using (module Transpose)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open PairingCancellation vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; cancel-left)

module Currying {S T C : CAT} (p : MAP S T) (f : MAP C S) (Π : DependentProduct p f) where
  g = DependentProduct.projection Π
  module Native = Existing.Currying 𝒯 M ℱ P p f Π using (evaluate; named-computation)

  module Factor {E : CAT} (t : MAP E T) (u : FunctorOver (pullback₂ {f = t} {p}) f) where
    module Chosen = Transpose p f Π t u using (over; comparison)
    module Names = Naming.NativeNames 𝒯 M ℱ P (Native.evaluate Chosen.over) u
      using (encode; decode; roundtrip)

    prescribed = Chosen.comparison ∙ Native.named-computation t Chosen.over ⁻¹

    comparison : FunctorOverIso (Native.evaluate Chosen.over) u
    comparison = Names.decode prescribed

    opaque
      computation : Names.encode comparison =₂ prescribed
      computation = Names.roundtrip prescribed

  module At {E : CAT} (t : MAP E T) (u v : FunctorOver t g) where
    module U = RelativeCurrying.At p f Π t using (uncurry; uncurry-isEquiv; reflect)
    module Source = Naming.NativeNames 𝒯 M ℱ P u v
      using (encode; decode; roundtrip; native-roundtrip; decode-congruence; congruence)
    module Target = Naming.NativeNames 𝒯 M ℱ P (Native.evaluate u) (Native.evaluate v)
      using (encode; decode; roundtrip; reflection; congruence; decode-congruence)
    module Higher = Calculus u v using (compose; inverse)
    cu = Native.named-computation t u
    cv = Native.named-computation t v

    prescribed : FunctorOverIso (Native.evaluate u) (Native.evaluate v) →
      (U.uncurry ∘ Over.name-over t g u) =₁ (U.uncurry ∘ Over.name-over t g v)
    prescribed Φ = cv ⁻¹ ∙ (Target.encode Φ ∙ cu)

    reflected-name : FunctorOverIso (Native.evaluate u) (Native.evaluate v) →
      Over.name-over t g u =₁ Over.name-over t g v
    reflected-name Φ = U.reflect (Over.name-over t g u) (Over.name-over t g v) (prescribed Φ)

    reflect : FunctorOverIso (Native.evaluate u) (Native.evaluate v) → FunctorOverIso u v
    reflect Φ = Source.decode (reflected-name Φ)

    evaluated-name : FunctorOverIso u v →
      Over.name-over (pullback₂ {f = t} {p}) f (Native.evaluate u) =₁
      Over.name-over (pullback₂ {f = t} {p}) f (Native.evaluate v)
    evaluated-name Ψ = cv ∙ ((U.uncurry ◁ Source.encode Ψ) ∙ cu ⁻¹)

    evaluate-identification : FunctorOverIso u v → FunctorOverIso (Native.evaluate u) (Native.evaluate v)
    evaluate-identification Ψ = Target.decode (evaluated-name Ψ)

    module Image (Φ : FunctorOverIso (Native.evaluate u) (Native.evaluate v)) where
      module Reflected = Computation.Reflection 𝒯 M U.uncurry-isEquiv
        (Over.name-over t g u) (Over.name-over t g v) using (computation)
      β = Source.encode (reflect Φ)
      ψ = Target.encode Φ

      opaque
        named-image : (U.uncurry ◁ β) =₂ prescribed Φ
        named-image = Reflected.computation (prescribed Φ) ∙
          (postWhisker U.uncurry ◁ Source.roundtrip (reflected-name Φ))

        endpoint-normalization : (cv ∙ (prescribed Φ ∙ cu ⁻¹)) =₂ ψ
        endpoint-normalization = cancel-right cu ψ ∙
          (isoComp-cong (cancel-inverse cv (ψ ∙ cu)) (idIso (cu ⁻¹)) ∙
            (isoComp-assoc-at cv (prescribed Φ) (cu ⁻¹)) ⁻¹)

        comparison : (cv ∙ ((U.uncurry ◁ β) ∙ cu ⁻¹)) =₂ ψ
        comparison = endpoint-normalization ∙
          isoComp-cong (idIso cv) (isoComp-cong named-image (idIso (cu ⁻¹)))

        computation : FunctorOverIso₂ (evaluate-identification (reflect Φ)) Φ
        computation = Target.reflection {Φ = evaluate-identification (reflect Φ)} {Ψ = Φ}
          (comparison ∙ Target.roundtrip (evaluated-name (reflect Φ)))

    module Roundtrip (Ψ : FunctorOverIso u v) where
      Φ = evaluate-identification Ψ
      θ = U.uncurry ◁ Source.encode Ψ
      module Reflected = Computation.Reflection 𝒯 M U.uncurry-isEquiv
        (Over.name-over t g u) (Over.name-over t g v) using (congruence; on-image)

      opaque
        cancel-endpoint : ((θ ∙ cu ⁻¹) ∙ cu) =₂ θ
        cancel-endpoint = isoComp-unitʳ-at θ ∙
          (isoComp-cong (idIso θ) (isoComp-inverseˡ-at cu) ∙ isoComp-assoc-at θ (cu ⁻¹) cu)

        input-image : prescribed Φ =₂ θ
        input-image = cancel-left cv θ ∙
          (isoComp-cong (idIso (cv ⁻¹))
            (isoComp-cong (idIso cv) cancel-endpoint ∙ isoComp-assoc-at cv (θ ∙ cu ⁻¹) cu) ∙
            isoComp-cong (idIso (cv ⁻¹))
              (isoComp-cong (Target.roundtrip (evaluated-name Ψ)) (idIso cu)))

        named-computation : reflected-name Φ =₂ Source.encode Ψ
        named-computation = Reflected.on-image (Source.encode Ψ) ∙ Reflected.congruence input-image

        computation : FunctorOverIso₂ (reflect (evaluate-identification Ψ)) Ψ
        computation = Higher.compose
          {Φ = reflect Φ} {Ψ = Source.decode (Source.encode Ψ)} {Ω = Ψ}
          (Source.native-roundtrip Ψ)
          (Source.decode-congruence {α = reflected-name Φ} {β = Source.encode Ψ} named-computation)

    opaque
      evaluate-congruence : {Φ Ψ : FunctorOverIso u v} → FunctorOverIso₂ Φ Ψ →
        FunctorOverIso₂ (evaluate-identification Φ) (evaluate-identification Ψ)
      evaluate-congruence {Φ} {Ψ} Ξ = Target.decode-congruence
        {α = evaluated-name Φ} {β = evaluated-name Ψ}
        (isoComp-cong (idIso cv)
          (isoComp-cong (postWhisker U.uncurry ◁ Source.congruence {Φ = Φ} {Ψ = Ψ} Ξ)
            (idIso (cu ⁻¹))))

      reflect-congruence : {Φ Ψ : FunctorOverIso (Native.evaluate u) (Native.evaluate v)} →
        FunctorOverIso₂ Φ Ψ → FunctorOverIso₂ (reflect Φ) (reflect Ψ)
      reflect-congruence {Φ} {Ψ} Ξ = Source.decode-congruence
        {α = reflected-name Φ} {β = reflected-name Ψ}
        (Reflected.congruence
          (isoComp-cong (idIso (cv ⁻¹))
            (isoComp-cong (Target.congruence {Φ = Φ} {Ψ = Ψ} Ξ) (idIso cu))))
        where
        module Reflected = Computation.Reflection 𝒯 M U.uncurry-isEquiv
          (Over.name-over t g u) (Over.name-over t g v) using (congruence)

      higher-reflection : {Φ Ψ : FunctorOverIso u v} →
        FunctorOverIso₂ (evaluate-identification Φ) (evaluate-identification Ψ) →
        FunctorOverIso₂ Φ Ψ
      higher-reflection {Φ} {Ψ} Ξ = Higher.compose
        {Φ = Φ} {Ψ = reflect (evaluate-identification Ψ)} {Ω = Ψ} (Roundtrip.computation Ψ)
        (Higher.compose
          {Φ = Φ} {Ψ = reflect (evaluate-identification Φ)} {Ω = reflect (evaluate-identification Ψ)}
          (reflect-congruence {Φ = evaluate-identification Φ} {Ψ = evaluate-identification Ψ} Ξ)
          (Higher.inverse {Φ = reflect (evaluate-identification Φ)} {Ψ = Φ} (Roundtrip.computation Φ)))
```
