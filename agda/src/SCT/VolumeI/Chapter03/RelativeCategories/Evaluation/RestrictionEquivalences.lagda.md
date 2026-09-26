# Restriction along an equivalence over the base

Restriction along an equivalence lifts native triangles and reflects
their identifications. The triangle of a lifted functor is chosen by
lifting its specified restricted image, rather than by discarding the
base comparison.

For reflection, transport both restricted triangles past their
associators, cancel the common base identification, and reflect through
prewhiskering by the equivalence. The returned identification retains
its triangle over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.RestrictionEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as ST
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open ST vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Restriction {A B C S : CAT} {a′ : MAP A S} (r : MAP B S) (f : MAP C S)
  (u : FunctorOver a′ r) (ee : IsEquiv (FunctorLift.lift u)) where
  e = FunctorLift.lift u
  θu = FunctorLift.comparison u

  module Factor (v : FunctorOver a′ f) where
    h = FunctorLift.lift v ∘ IsEquiv.inverse ee
    β : (h ∘ e) =₁ FunctorLift.lift v
    β = comp-unitʳ (FunctorLift.lift v) ∙
      ((FunctorLift.lift v ◁ (IsEquiv.sectionIso ee) ⁻¹) ∙
        comp-assoc e (IsEquiv.inverse ee) (FunctorLift.lift v))
    κ = comp-assoc e h f
    desired = FunctorLift.comparison v ∙ (f ◁ β)
    raw = θu ⁻¹ ∙ (desired ∙ κ)
    lifted : FunctorLift (preWhisker e) raw
    lifted = preWhisker-lift e ee raw

    value : FunctorOver r f
    value = record { lift = h ; comparison = FunctorLift.lift lifted }

    abstract
      matching : FunctorLift.comparison (compose-over value u) =₂ desired
      matching = cancel-right κ desired ∙
        (isoComp-cong (cancel-inverse θu (desired ∙ κ)) (idIso (κ ⁻¹)) ∙
          ((isoComp-assoc-at θu raw (κ ⁻¹)) ⁻¹ ∙
            isoComp-cong (idIso θu)
              (isoComp-cong (FunctorLift.comparison lifted) (idIso (κ ⁻¹)))))

      comparison : FunctorOverIso (compose-over value u) v
      comparison = record { underlying = β ; compatible = matching ⁻¹ }

  module Reflect (v w : FunctorOver r f)
    (Φ : FunctorOverIso (compose-over v u) (compose-over w u)) where
    vh = FunctorLift.lift v
    wh = FunctorLift.lift w
    θv = FunctorLift.comparison v
    θw = FunctorLift.comparison w
    lifted : FunctorLift (preWhisker e) (FunctorOverIso.underlying Φ)
    lifted = preWhisker-lift e ee (FunctorOverIso.underlying Φ)
    δ = FunctorLift.lift lifted
    κv = comp-assoc e vh f
    κw = comp-assoc e wh f
    middle = (f ◁ δ) ▷ e

    abstract
      transported : changeEndpoints κv κw middle =₂ (f ◁ (δ ▷ e))
      transported = square-to-changeEndpoints κv κw middle (f ◁ (δ ▷ e)) (whisker-mixed-at δ e f)

      after-restriction :
        changeEndpoints κv θu ((θw ▷ e) ∙ middle) =₂ changeEndpoints κv θu (θv ▷ e)
      after-restriction = FunctorOverIso.compatible Φ ∙
        (isoComp-cong (idIso (FunctorLift.comparison (compose-over w u)))
          (postWhisker f ◁ FunctorLift.comparison lifted) ∙
          (isoComp-cong (idIso (FunctorLift.comparison (compose-over w u))) transported ∙
            (changeEndpoints-comp κv κw θu (θw ▷ e) middle) ⁻¹))

      matching : (θw ∙ (f ◁ δ)) =₂ θv
      matching = equiv-reflect (preWhisker-isEquiv e ee (f ∘ vh) r) (θw ∙ (f ◁ δ)) θv
        (changeEndpoints-reflect κv θu ((θw ▷ e) ∙ middle) (θv ▷ e) after-restriction ∙
          preWhisker-isoComp-at θw (f ◁ δ) e)

      comparison : FunctorOverIso v w
      comparison = record { underlying = δ ; compatible = matching }
```
