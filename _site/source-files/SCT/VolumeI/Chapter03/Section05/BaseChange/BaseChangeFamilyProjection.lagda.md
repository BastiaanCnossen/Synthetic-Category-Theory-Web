# Projecting a base-changed family

After projection from the target pullback, base change is restriction
along the first projection from the source pullback. The comparison
includes the pullback matching identification and both source
associators. This calculation applies to an arbitrary family.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (universal)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)

import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.PulledFamilies as PulledFamilies

module Change {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  C′ = Pullback f p
  D′ = Pullback g p
  f′ : MAP C′ S
  f′ = pullback₂
  g′ : MAP D′ S
  g′ = pullback₂
  projection : FunctorOver (p ∘ f′) f
  projection = record { lift = pullback₁ ; comparison = pullbackMatch }
  module Arg = Argument projection
  module Project = Families p g f′

  module At {X : CAT} (v : FunctorOver (f ∘ pr₂ {C = X}) g) where
    module Raw = PulledFamilies.Change.At 𝒯 M ℱ P
      {C = C} {D = D} {S = S} {T = T} p f g {X = X} v
      using (R; h; θ; Z; d; A; b; κ; tail; cone; pulled)
    open Raw public
    restricted = compose-over v (Arg.family X)

    raw : FunctorOver (p ∘ (f′ ∘ pr₂ {C = X})) g
    raw = record { lift = h ∘ R ; comparison = Cone.match cone }

    parameter-triangle : FunctorOver (p ∘ (f′ ∘ pr₂ {C = X})) (f ∘ pr₂ {C = X})
    parameter-triangle = change-source Z (Arg.family X)
    parameter-cone : Cone (f ∘ pr₂ {C = X}) p (X × C′)
    parameter-cone = record { left = R ; right = f′ ∘ pr₂ ; match = FunctorLift.comparison parameter-triangle }
    acted-cone = Action.value p v parameter-cone

    abstract
      normalized : Cone.match cone =₂ (Z ∙ FunctorLift.comparison restricted)
      normalized = isoComp-cong (idIso Z)
        ((isoComp-assoc-at d ((A ⁻¹) ∙ (b ∙ κ)) tail) ⁻¹ ∙
          (isoComp-cong (idIso d) ((isoComp-assoc-at (A ⁻¹) (b ∙ κ) tail) ⁻¹) ∙
            isoComp-cong (idIso d) (isoComp-cong (idIso (A ⁻¹)) ((isoComp-assoc-at b κ tail) ⁻¹))))

      raw-comparison : FunctorOverIso raw (change-source Z restricted)
      raw-comparison = triangle-identification _ _ _ normalized

      projection-comparison : FunctorOverIso (Project.forward pulled) restricted
      projection-comparison = compose-iso-over (source-change-inverse Z restricted)
        (change-source-iso (Z ⁻¹)
          (compose-iso-over raw-comparison (Target.forward-backward p g (f′ ∘ pr₂) raw)))


    abstract
      action-comparison : FunctorOverIso pulled (lift-triangle acted-cone)
      action-comparison = Target.backward-identification p g (f′ ∘ pr₂)
        (compose-iso-over (inverse-iso-over (compose-source-change Z (Arg.family X) v)) raw-comparison)
```

## Identifications of base-changed families

```agda
module Identification {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  module Native = Change p f g
  abstract
    comparison : {X : CAT} {u v : FunctorOver (f ∘ pr₂ {C = X}) g} → FunctorOverIso u v →
      FunctorOverIso (Native.At.pulled u) (Native.At.pulled v)
    comparison {X} {u} {v} Φ = Native.Project.reflect _ _
      (compose-iso-over (inverse-iso-over (Native.At.projection-comparison v))
        (compose-iso-over (prewhisker-over (Native.Arg.family X) Φ) (Native.At.projection-comparison u)))
```
