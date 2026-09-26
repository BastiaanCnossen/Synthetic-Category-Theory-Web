# Cancelling an intermediate change of structure

Changing the target structure of a functor and the source structure of
the next functor by inverse identifications cancels in their composite.
The proof retains the prewhiskered identification and the associator.
It is used when a base-changed functor is regarded over the original base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

change-target-back : {C D S : CAT} {f : MAP C S} {g g′ : MAP D S} →
  g′ =₁ g → FunctorOver f g → FunctorOver f g′
change-target-back γ u = record { lift = FunctorLift.lift u
  ; comparison = FunctorLift.comparison u ∙ (γ ▷ FunctorLift.lift u) }

abstract
  source-change-composite : {C D S : CAT} {f f′ f″ : MAP C S} {g : MAP D S}
    (β : f′ =₁ f″) (α : f =₁ f′) (u : FunctorOver f g) →
    FunctorOverIso (change-source β (change-source α u)) (change-source (β ∙ α) u)
  source-change-composite β α u = triangle-identification _ _ _
    ((isoComp-assoc-at β α (FunctorLift.comparison u)) ⁻¹)

  compose-source-change : {B C D S : CAT} {f f′ : MAP B S} {g : MAP C S} {h : MAP D S}
    (α : f =₁ f′) (u : FunctorOver f g) (v : FunctorOver g h) →
    FunctorOverIso (compose-over v (change-source α u)) (change-source α (compose-over v u))
  compose-source-change {h = h} α u v = triangle-identification _ _ _
    (isoComp-assoc-at α (FunctorLift.comparison u)
      ((FunctorLift.comparison v ▷ FunctorLift.lift u) ∙
        (comp-assoc (FunctorLift.lift u) (FunctorLift.lift v) h) ⁻¹))

  compose-source-change-underlying : {B C D S : CAT}
    {f f′ : MAP B S} {g : MAP C S} {h : MAP D S}
    (α : f =₁ f′) (u : FunctorOver f g) (v : FunctorOver g h) →
    FunctorOverIso.underlying (compose-source-change α u v) =₂
      idIso (FunctorLift.lift v ∘ FunctorLift.lift u)
  compose-source-change-underlying α u v = idIso _

module Cancellation {B C D S : CAT} {f : MAP B S} {g g′ : MAP C S} {h : MAP D S}
  (γ : g′ =₁ g) (u : FunctorOver f g) (v : FunctorOver g h) where
  k = FunctorLift.lift u
  j = FunctorLift.lift v
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  δ = γ ▷ k
  τ = θv ▷ k
  assoc = comp-assoc k j h

  abstract
    matching : FunctorLift.comparison (compose-over (change-source (γ ⁻¹) v) (change-target-back γ u)) =₂
      FunctorLift.comparison (compose-over v u)
    matching = isoComp-cong (idIso θu) (cancel-inverse δ (τ ∙ assoc ⁻¹)) ∙
      (isoComp-assoc-at θu δ (δ ⁻¹ ∙ (τ ∙ assoc ⁻¹)) ∙
        (isoComp-cong (idIso (θu ∙ δ)) (isoComp-assoc-at (δ ⁻¹) τ (assoc ⁻¹)) ∙
          isoComp-cong (idIso (θu ∙ δ))
            (isoComp-cong
              (isoComp-cong (pre-inverse γ k) (idIso τ) ∙ preWhisker-isoComp-at (γ ⁻¹) θv k)
              (idIso (assoc ⁻¹)))))

    comparison : FunctorOverIso
      (compose-over (change-source (γ ⁻¹) v) (change-target-back γ u)) (compose-over v u)
    comparison = triangle-identification _ _ _ matching

abstract
  compose-target-change : {B C D S : CAT} {f : MAP B S} {g g′ : MAP C S} {h : MAP D S}
    (α : g =₁ g′) (u : FunctorOver f g′) (v : FunctorOver g h) →
    FunctorOverIso (compose-over (change-source α v) u) (compose-over v (change-target-back α u))
  compose-target-change {h = h} α u v = triangle-identification _ _ _
    ((isoComp-assoc-at (FunctorLift.comparison u) (α ▷ FunctorLift.lift u)
      ((FunctorLift.comparison v ▷ FunctorLift.lift u) ∙
        (comp-assoc (FunctorLift.lift u) (FunctorLift.lift v) h) ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso (FunctorLift.comparison u))
        (isoComp-assoc-at (α ▷ FunctorLift.lift u) (FunctorLift.comparison v ▷ FunctorLift.lift u)
          ((comp-assoc (FunctorLift.lift u) (FunctorLift.lift v) h) ⁻¹) ∙
          isoComp-cong (preWhisker-isoComp-at α (FunctorLift.comparison v) (FunctorLift.lift u))
            (idIso ((comp-assoc (FunctorLift.lift u) (FunctorLift.lift v) h) ⁻¹))))
```
