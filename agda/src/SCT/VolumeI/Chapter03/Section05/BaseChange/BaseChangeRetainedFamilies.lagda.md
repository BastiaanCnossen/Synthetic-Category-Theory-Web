# Base change and retained relative families

Compare two ways of composing relative families after base change.
The essential square says that retaining a base-changed family and then
projecting its argument agrees with first projecting the argument and
then retaining the original family. Both routes retain the same parameter.

After forgetting that parameter, the square is the native computation
of the pullback lift. Choose the other projection by the product laws,
and recover the triangle over the base. This gives a comparison of
whole families without a naturality assumption on pointwise compositors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeRetainedFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter03.Section05.Currying.ArgumentFamilyProjection 𝒯 M ℱ P using (module Project)
open import SCT.VolumeI.Chapter03.Section05.Currying.FamilyProjection 𝒯 M ℱ P using (projection)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target; forward-composite)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P
  using (module Retained; module ProjectionReflection)

module ArgumentOver {C S T : CAT} (p : MAP S T) (f : MAP C T) (X : CAT) where
  q : MAP (Pullback f p) S
  q = pullback₂
  π : FunctorOver (p ∘ q) f
  π = record { lift = pullback₁ ; comparison = pullbackMatch }
  Z = comp-assoc (pr₂ {C = X}) q p
  argument = Argument.family π X
  over = change-source Z argument
  shifted-projection = change-source Z (projection (p ∘ q) X)
  post-projection = postbase p (projection q X)

  opaque
    projection-shift : FunctorOverIso shifted-projection post-projection
    projection-shift = triangle-identification pr₂ _ _
      ((isoComp-unitˡ-at Z ∙
        isoComp-cong (postWhisker-idIso p (q ∘ pr₂)) (idIso Z)) ⁻¹ ∙ isoComp-unitʳ-at Z)

    projected : FunctorOverIso (compose-over (projection f X) over)
      (Target.forward p f (q ∘ pr₂) (projection q X))
    projected = compose-iso-over (inverse-iso-over (Target.forward-normalization p f (q ∘ pr₂) (projection q X)))
      (compose-iso-over (postwhisker-over π projection-shift)
      (compose-iso-over (inverse-iso-over (compose-source-change Z (projection (p ∘ q) X) π))
      (compose-iso-over (change-source-iso Z (Project.comparison π X))
        (compose-source-change Z argument (projection f X)))))

module Projected {X C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T)
  (u : FunctorOver (f ∘ pr₂ {C = X}) g) where
  module Input = ArgumentOver p f X
  module B = Change p f g using (module At)
  module Value = B.At u using (pulled; raw; raw-comparison)
  pulled = Value.pulled
  raw = Value.raw

  opaque
    comparison : FunctorOverIso (Target.forward p g (Input.q ∘ pr₂) pulled)
      (compose-over u Input.over)
    comparison = compose-iso-over (inverse-iso-over (compose-source-change Input.Z Input.argument u))
      (compose-iso-over Value.raw-comparison (Target.forward-backward p g (Input.q ∘ pr₂) raw))

module RetainedChange {X C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T)
  (u : FunctorOver (f ∘ pr₂ {C = X}) g) where
  module Input = ArgumentOver p f X
  module Output = ArgumentOver p g X
  module B = Projected p f g u
  module U = Retained f g u
  module V = Retained Input.q Output.q B.pulled
  changed = postbase p V.over
  source = compose-over Output.over changed
  target = compose-over U.over Input.over
  module Reflect = ProjectionReflection pr₂ g source target

  opaque
    source-to-common : FunctorOverIso (compose-over Reflect.projection source) (compose-over u Input.over)
    source-to-common = compose-iso-over B.comparison
      (compose-iso-over (Target.Identification.comparison p g (Input.q ∘ pr₂) V.forget-retained)
      (compose-iso-over (inverse-iso-over (forward-composite p g (projection Output.q X) V.over))
      (compose-iso-over (prewhisker-over changed Output.projected)
        (inverse-iso-over (associator-over changed Output.over Reflect.projection)))))

    target-to-common : FunctorOverIso (compose-over Reflect.projection target) (compose-over u Input.over)
    target-to-common = compose-iso-over (prewhisker-over Input.over U.forget-retained)
      (inverse-iso-over (associator-over Input.over U.over Reflect.projection))

    projected : FunctorOverIso (compose-over Reflect.projection source) (compose-over Reflect.projection target)
    projected = compose-iso-over (inverse-iso-over target-to-common) source-to-common

  first-source = pair-β₁ pr₁ V.value ∙
    (((comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (pullback₁ {f = g} {p} ∘ pr₂)) ▷ V.lift) ∙
      (comp-assoc V.lift (FunctorLift.lift Output.over) pr₁) ⁻¹)
  first-target = (comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (pullback₁ {f = f} {p} ∘ pr₂)) ∙
    ((pair-β₁ pr₁ U.value ▷ FunctorLift.lift Input.over) ∙
      (comp-assoc (FunctorLift.lift Input.over) U.lift pr₁) ⁻¹)
  first = first-target ⁻¹ ∙ first-source
  second = FunctorOverIso.underlying projected
  underlying = pair-iso first second

  comparison : FunctorOverIso source target
  comparison = Reflect.FromImage.comparison projected underlying (pair-iso-β₂ first second)

module CompositeFamilies {X A B C S T : CAT} (p : MAP S T)
  (f : MAP A T) (g : MAP B T) (h : MAP C T)
  (u : FunctorOver (f ∘ pr₂ {C = X}) g)
  (v : FunctorOver (g ∘ pr₂ {C = X}) h) where
  module Square = RetainedChange p f g u
  module Outer = Projected p g h v
  composite = compose-over v Square.U.over
  module Whole = Projected p f h composite
  source = compose-over Outer.pulled Square.V.over
  target = Whole.pulled
  q = Square.Input.q ∘ pr₂ {C = X}

  opaque
    projected : FunctorOverIso (Target.forward p h q source) (Target.forward p h q target)
    projected = compose-iso-over (inverse-iso-over Whole.comparison)
      (compose-iso-over (inverse-iso-over (associator-over Square.Input.over Square.U.over v))
      (compose-iso-over (postwhisker-over v Square.comparison)
      (compose-iso-over (associator-over Square.changed Square.Output.over v)
      (compose-iso-over (prewhisker-over Square.changed Outer.comparison)
        (forward-composite p h Outer.pulled Square.V.over)))))

    comparison : FunctorOverIso source target
    comparison = compose-iso-over (Target.Recovery.comparison p h q target)
      (compose-iso-over (Target.backward-identification p h q projected)
        (inverse-iso-over (Target.Recovery.comparison p h q source)))
```
