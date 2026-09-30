# Retaining a parameter in relative families

Pair a relative family with its parameter projection. The resulting
functor still lies over the same base, and forgetting the parameter
recovers the original family through a native comparison. Relative
identifications also retain their triangles under this construction.

For composition, choose the comparison by its two product projections.
The first retains the parameter; the second is the known native
comparison after forgetting it. `ProjectionReflection` recovers the
triangle over the base from this prescribed second image.

These are endpoint normalizations for parameterized relative operations.
A compatible associator family and its restriction computations remain
separate work.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₂)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)

-- Retain the parameter and recover the original family after projection.
module Retained {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (v : FunctorOver (f ∘ pr₂ {C = X}) g) where
  value = FunctorLift.lift v
  θ = FunctorLift.comparison v
  lift = pair (pr₁ {C = X}) value
  evaluation = pair-β₂ (pr₁ {C = X}) value
  assoc = comp-assoc lift pr₂ g
  triangle = θ ∙ ((g ◁ evaluation) ∙ assoc)

  over : FunctorOver (f ∘ pr₂ {C = X}) (g ∘ pr₂ {C = X})
  over = record { lift = lift ; comparison = triangle }

  projection : FunctorOver (g ∘ pr₂ {C = X}) g
  projection = record { lift = pr₂ ; comparison = idIso (g ∘ pr₂) }

  opaque
    projected-triangle : FunctorLift.comparison (compose-over projection over) =₂
      (θ ∙ (g ◁ evaluation))
    projected-triangle = cancel-right assoc (θ ∙ (g ◁ evaluation)) ∙
      (isoComp-cong ((isoComp-assoc-at θ (g ◁ evaluation) assoc) ⁻¹) (idIso (assoc ⁻¹)) ∙
        isoComp-cong (idIso triangle)
          (isoComp-unitˡ-at (assoc ⁻¹) ∙
            isoComp-cong (preWhisker-idIso (g ∘ pr₂) lift) (idIso (assoc ⁻¹))))

    forget-retained : FunctorOverIso (compose-over projection over) v
    forget-retained = record { underlying = evaluation ; compatible = projected-triangle ⁻¹ }

module Identification {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (u v : FunctorOver (f ∘ pr₂ {C = X}) g) (Φ : FunctorOverIso u v) where
  module U = Retained f g u
  module V = Retained f g v
  α = FunctorOverIso.underlying Φ
  δ = pair-cong (idIso (pr₁ {C = X})) α

  opaque
    evaluated-square : ((g ◁ V.evaluation) ∙ (g ◁ (pr₂ ◁ δ))) =₂
      ((g ◁ α) ∙ (g ◁ U.evaluation))
    evaluated-square = postWhisker-isoComp-at g α U.evaluation ∙
      ((postWhisker g ◁ pair-cong-triangle₂ (idIso (pr₁ {C = X})) α) ∙
        (postWhisker-isoComp-at g V.evaluation (pr₂ ◁ δ)) ⁻¹)

    tail-square : (((g ◁ V.evaluation) ∙ V.assoc) ∙ ((g ∘ pr₂) ◁ δ)) =₂
      ((g ◁ α) ∙ ((g ◁ U.evaluation) ∙ U.assoc))
    tail-square = paste-iso-squares U.assoc V.assoc (g ◁ U.evaluation) (g ◁ V.evaluation)
      ((g ∘ pr₂) ◁ δ) (g ◁ (pr₂ ◁ δ)) (g ◁ α)
      (postWhisker-comp-at δ pr₂ g) evaluated-square

    triangle : (V.triangle ∙ ((g ∘ pr₂) ◁ δ)) =₂ U.triangle
    triangle = isoComp-unitˡ-at U.triangle ∙
      paste-iso-squares ((g ◁ U.evaluation) ∙ U.assoc) ((g ◁ V.evaluation) ∙ V.assoc)
        U.θ V.θ ((g ∘ pr₂) ◁ δ) (g ◁ α) (idIso (f ∘ pr₂))
        tail-square ((isoComp-unitˡ-at U.θ) ⁻¹ ∙ FunctorOverIso.compatible Φ)

    comparison : FunctorOverIso U.over V.over
    comparison = record { underlying = δ ; compatible = triangle }

module ProjectionReflection {A B C S : CAT} (r : MAP B C) (h : MAP C S)
  {e : MAP A S} (x y : FunctorOver e (h ∘ r)) where
  projection : FunctorOver (h ∘ r) h
  projection = record { lift = r ; comparison = idIso (h ∘ r) }
  px = compose-over projection x
  py = compose-over projection y

  module Triangle (z : FunctorOver e (h ∘ r)) where
    θ = FunctorLift.comparison z
    associator = comp-assoc (FunctorLift.lift z) r h
    ψ = FunctorLift.comparison (compose-over projection z)
    opaque
      normalize : ψ =₂ (θ ∙ associator ⁻¹)
      normalize = isoComp-cong (idIso θ)
        (isoComp-unitˡ-at (associator ⁻¹) ∙
          isoComp-cong (preWhisker-idIso (h ∘ r) (FunctorLift.lift z)) (idIso (associator ⁻¹)))
      recover : (ψ ∙ associator) =₂ θ
      recover = isoComp-unitʳ-at θ ∙
        (isoComp-cong (idIso θ) (isoComp-inverseˡ-at associator) ∙
          (isoComp-assoc-at θ (associator ⁻¹) associator ∙ isoComp-cong normalize (idIso associator)))

  module X = Triangle x
  module Y = Triangle y

  module FromImage (Φ : FunctorOverIso px py) (α : FunctorLift.lift x =₁ FunctorLift.lift y)
    (image : (r ◁ α) =₂ FunctorOverIso.underlying Φ) where
    opaque
      square : (Y.ψ ∙ (h ◁ (r ◁ α))) =₂ X.ψ
      square = FunctorOverIso.compatible Φ ∙
        isoComp-cong (idIso Y.ψ) (postWhisker h ◁ image)

      triangle : (Y.θ ∙ ((h ∘ r) ◁ α)) =₂ X.θ
      triangle = X.recover ∙
        (isoComp-cong square (idIso X.associator) ∙
        ((isoComp-assoc-at Y.ψ (h ◁ (r ◁ α)) X.associator) ⁻¹ ∙
        (isoComp-cong (idIso Y.ψ) (postWhisker-comp-at α r h) ∙
        (isoComp-assoc-at Y.ψ Y.associator ((h ∘ r) ◁ α) ∙
          isoComp-cong (Y.recover ⁻¹) (idIso ((h ∘ r) ◁ α))))))

      comparison : FunctorOverIso x y
      comparison = record { underlying = α ; compatible = triangle }

module RetainedComposite {X A B C S : CAT} (f : MAP A S) (g : MAP B S) (h : MAP C S)
  (u : FunctorOver (f ∘ pr₂ {C = X}) g)
  (v : FunctorOver (g ∘ pr₂ {C = X}) h) where
  module U = Retained f g u
  module V = Retained g h v
  composite = compose-over v U.over
  module W = Retained f h composite
  source = compose-over V.over U.over
  target = W.over
  module Reflect = ProjectionReflection pr₂ h source target

  opaque
    projected : FunctorOverIso (compose-over Reflect.projection source) (compose-over Reflect.projection target)
    projected = compose-iso-over (inverse-iso-over W.forget-retained)
      (compose-iso-over (prewhisker-over U.over V.forget-retained)
        (inverse-iso-over (associator-over U.over V.over Reflect.projection)))

  first-source = pair-β₁ pr₁ U.value ∙
    ((pair-β₁ pr₁ V.value ▷ U.lift) ∙ (comp-assoc U.lift V.lift pr₁) ⁻¹)
  first-target = pair-β₁ pr₁ W.value
  first = first-target ⁻¹ ∙ first-source
  second = FunctorOverIso.underlying projected
  underlying = pair-iso first second

  comparison : FunctorOverIso source target
  comparison = Reflect.FromImage.comparison projected underlying (pair-iso-β₂ first second)

```
