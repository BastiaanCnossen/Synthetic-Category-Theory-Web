# Pasting the Beck–Chevalley evaluation cone

Apply a relative functor to a cone, lift into the new evaluation domain,
and then pass to the original domain. The resulting cone agrees with
first pasting across the base-change square and then applying the
projected relative functor. The comparison retains both projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConePasting 𝒯 M ℱ P using (module Pasting)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyDomain 𝒯 M ℱ P using (module Domain)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle; module ToCone)

module Pasted {S T S′ T′ D K X : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (g : MAP D T) (k : MAP K T′)
  (u : FunctorOver k (pullback₂ {f = g} {b})) (s : Cone k (Cone.right square) X) where
  module Dom = Domain p b square g
  open Dom using (h; p′; t; j₂; projected; into; into-over)
  module PasteK = PasteCones k b (coneSwap square)
  module PasteT = PasteCones t b (coneSwap square)
  lifted-cone = Action.value p′ u s
  ℓ = pullbackLift lifted-cone
  β = pullbackLift-β₂ lifted-cone
  target = Action.value p (Target.forward b g k u) (PasteK.flatten s)
  over = compose-over into-over (postbase h (lift-triangle lifted-cone))

  first = coneIso-compose (coneIso-pre ℓ (pullbackLift-β Dom.cone))
    (coneIso-inverse (conePre-assoc ℓ into (pullbackCone g p)))
  normalized = coneIso-compose (coneIso-pre ℓ Dom.normalization) first
  restricted = coneIso-compose (Action.restriction p projected ℓ (PasteT.flatten (pullbackCone t p′))) normalized
  pasted = coneIso-compose (Action.map-iso p projected (PasteT.flatten-pre ℓ (pullbackCone t p′))) restricted
  lifted = coneIso-compose (Action.map-iso p projected (PasteT.flatten-iso (pullbackLift-β lifted-cone))) pasted
  acted = coneIso-compose (Action.map-iso p projected (Pasting.flatten-action p b (coneSwap square) u s)) lifted
  composed = coneIso-compose (coneIso-inverse (compose-action p (postbase b u) projected (PasteK.flatten s))) acted
  cones : ConeIso (conePre (into ∘ ℓ) (pullbackCone g p)) target
  cones = coneIso-compose
    (action-identification p (inverse-iso-over (Target.forward-normalization b g k u)) (PasteK.flatten s)) composed

  private
    tail = (pullbackLift-β₂ Dom.cone ▷ ℓ) ∙ (comp-assoc ℓ into (pullback₂ {f = g} {p})) ⁻¹
    assoc = comp-assoc ℓ j₂ h
    θ = FunctorLift.comparison over

  abstract
    normalized-right : ConeIso.rightIso normalized =₂ tail
    normalized-right = isoComp-unitˡ-at tail ∙
      isoComp-cong (preWhisker-idIso (h ∘ j₂) ℓ) (idIso tail)

    restricted-right : ConeIso.rightIso restricted =₂ tail
    restricted-right = normalized-right ∙ isoComp-unitˡ-at (ConeIso.rightIso normalized)

    pasted-right : ConeIso.rightIso pasted =₂ (assoc ∙ tail)
    pasted-right = isoComp-cong (idIso assoc) restricted-right

    lifted-right : ConeIso.rightIso lifted =₂ θ
    lifted-right = (isoComp-assoc-at (h ◁ β) assoc tail) ⁻¹ ∙
      isoComp-cong (idIso (h ◁ β)) pasted-right

    acted-right : ConeIso.rightIso acted =₂ θ
    acted-right = lifted-right ∙ isoComp-unitˡ-at (ConeIso.rightIso lifted)

    composed-right : ConeIso.rightIso composed =₂ θ
    composed-right = acted-right ∙
      (isoComp-unitˡ-at (ConeIso.rightIso acted) ∙
        isoComp-cong (inverse-identity (h ∘ Cone.right s)) (idIso (ConeIso.rightIso acted)))

    right-comparison : ConeIso.rightIso cones =₂ θ
    right-comparison = composed-right ∙ isoComp-unitˡ-at (ConeIso.rightIso composed)

    native-comparison : FunctorOverIso over (lift-triangle target)
    native-comparison = ToCone.comparison target over cones right-comparison
```
