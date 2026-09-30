# Naturality of enriched dependent uncurrying

The comparison for induced dependent-product functors holds on whole
relative functor categories. Evaluate their universal families, apply
the native evaluation comparison, and reflect back. This is the
naturality used to compare cospans through the uncurrying equivalences.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyLifting 𝒯 M ℱ P using (action)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.CoherentRelativeFamilyLifting 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingFamilies 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.DependentProductEvaluationNaturality 𝒯 M ℱ P using (module Naturality)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

-- Only evaluation is needed here. In particular this wrapper does not
-- specialize the factorization and inverse of enriched uncurrying.
module Uncurrying {S T C K : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) (k : MAP K T) where
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  module Evaluated = Evaluation p f Π k using (functor; module At)
  module Native = Currying p f Π using (evaluate)
  functor : MAP (FunOver k g) (FunOver k′ f)
  functor = Evaluated.functor
  abstract
    evaluate-identification : {A : CAT} {t : MAP A T} {u v : FunctorOver t g} →
      FunctorOverIso u v → FunctorOverIso (Native.evaluate u) (Native.evaluate v)
    evaluate-identification Φ = postwhisker-over ε (Change.Identification.comparison p Φ)

module UniversalFamily {S T C K : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) (k : MAP K T) where
  module U = Uncurrying p f Π k using (g; k′; functor; evaluate-identification; module Evaluated; module Native)
  X = FunOver k U.g
  module F = U.Evaluated.At X using (inclusion; family-comparison)
  abstract
    comparison : FunctorOverIso (family U.k′ f U.functor)
      (compose-over (U.Native.evaluate (universal k U.g)) F.inclusion)
    comparison = compose-iso-over
      (prewhisker-over F.inclusion (U.evaluate-identification (family-identity k U.g)))
      (compose-iso-over (F.family-comparison (id X))
        (family-identification U.k′ f ((comp-unitʳ U.functor) ⁻¹)))

module NaturalComparison {S T C D K : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g)
  (u : FunctorOver f g) (k : MAP K T)
  (induced : FunctorOver (DependentProduct.projection ΠC) (DependentProduct.projection ΠD))
  (native-comparison : FunctorOverIso
    (Currying.evaluate p g ΠD (compose-over induced (universal k (DependentProduct.projection ΠC))))
    (compose-over u (Currying.evaluate p f ΠC (universal k (DependentProduct.projection ΠC))))) where
  module Source = Uncurrying p f ΠC k using (g; k′; functor; module Native)
  module Target = Uncurrying p g ΠD k using (g; functor; evaluate-identification; module Evaluated; module Native)
  module Before = Postcompose k induced using (functor; family-comparison)
  module After = Postcompose Source.k′ u using (functor)
  X = FunOver k Source.g
  module Family = Target.Evaluated.At X using (inclusion; family-comparison)
  module Original = UniversalFamily p f ΠC k using (comparison)
  w : FunctorOver (k ∘ pr₂ {C = X}) Source.g
  w = universal k Source.g
  inclusion : FunctorOver (Source.k′ ∘ pr₂ {C = X}) (pullback₂ {f = k ∘ pr₂ {C = X}} {p})
  inclusion = Family.inclusion
  normal : FunctorOver (Source.k′ ∘ pr₂ {C = X}) g
  normal = compose-over u (compose-over (Source.Native.evaluate w) inclusion)

  abstract
    before-evaluation : FunctorOverIso
      (Target.Native.evaluate (family k Target.g Before.functor))
      (Target.Native.evaluate (compose-over induced w))
    before-evaluation = Target.evaluate-identification Before.family-comparison
    left-family : FunctorOverIso (family Source.k′ g (Target.functor ∘ Before.functor)) normal
    left-family = compose-iso-over (associator-over inclusion (Source.Native.evaluate w) u)
      (compose-iso-over (prewhisker-over inclusion native-comparison)
        (compose-iso-over (prewhisker-over inclusion before-evaluation)
          (Family.family-comparison Before.functor)))
    right-family : FunctorOverIso (family Source.k′ g (After.functor ∘ Source.functor)) normal
    right-family = compose-iso-over (postwhisker-over u Original.comparison)
      (postcompose-family Source.k′ u Source.functor)
    family-comparison : FunctorOverIso
      (family Source.k′ g (Target.functor ∘ Before.functor))
      (family Source.k′ g (After.functor ∘ Source.functor))
    family-comparison = compose-iso-over {f = Source.k′ ∘ pr₂ {C = X}} {g = g}
      (inverse-iso-over right-family) left-family
  module Lifted = Families Source.k′ g (Target.functor ∘ Before.functor)
    (After.functor ∘ Source.functor)
    using (action; Result; result; result-image)
  lifted : Lifted.Result family-comparison
  lifted = Lifted.result family-comparison
  abstract
    comparison : (Target.functor ∘ Before.functor) =₁ (After.functor ∘ Source.functor)
    comparison = Lifted.Result.comparison lifted
    evaluated-computation : FunctorOverIso₂ (Lifted.action comparison) family-comparison
    evaluated-computation = Lifted.Result.full-image lifted
    evaluated-image : FunctorOverIso.underlying (action Source.k′ g comparison) =₂
      FunctorOverIso.underlying family-comparison
    evaluated-image = Lifted.result-image family-comparison lifted

-- Prove the family calculation before substituting the chosen transpose.
-- This keeps the proof independent of the implementation of that choice.
module Natural {S T C D K : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g)
  (u : FunctorOver f g) (k : MAP K T) where
  open NaturalComparison p f g ΠC ΠD u k (Induced.over p f g ΠC ΠD u)
    (Naturality.comparison p f g ΠC ΠD u (universal k (DependentProduct.projection ΠC))) public
    using (comparison; evaluated-image; evaluated-computation; family-comparison; lifted; module Lifted)
```
