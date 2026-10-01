# Coproducts of categories over a fixed base

Copair the total functors and lift the base triangle with its prescribed
restrictions. The two beta comparisons are comparisons over the base.
Conversely, comparisons on the two summands determine a comparison of
relative functors. Everything is constructed in the absolute context.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.Coproducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) (B : Coproducts.CoproductStructure 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.IsomorphismRestriction 𝒯 M B
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PrecompositionCompatibility 𝒯 M ℱ P using (module Restriction)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

abstract
  coproduct-reflect-Iso₂ : {C D E : CAT} {h k : MAP (C ⊔ D) E} {α β : h =₁ k} →
    (α ▷ in₁) =₂ (β ▷ in₁) → (α ▷ in₂) =₂ (β ▷ in₂) → α =₂ β
  coproduct-reflect-Iso₂ {h = h} {k} {α} {β} first second =
    equiv-reflect (coproductIsoRestriction-isEquiv h k) α β
      ((pair-pre (preWhisker in₁) (preWhisker in₂) β) ⁻¹ ∙
        (pair-cong first second ∙ pair-pre (preWhisker in₁) (preWhisker in₂) α))

module Sum {C D S : CAT} (p : MAP C S) (q : MAP D S) where
  projection = copair p q
  first : FunctorOver p projection
  first = record { lift = in₁ ; comparison = copair-β₁ p q }
  second : FunctorOver q projection
  second = record { lift = in₂ ; comparison = copair-β₂ p q }

  module Copair {E : CAT} {r : MAP E S} (u : FunctorOver p r) (v : FunctorOver q r) where
    F = copair (FunctorLift.lift u) (FunctorLift.lift v)
    α = copair-β₁ (FunctorLift.lift u) (FunctorLift.lift v)
    β = copair-β₂ (FunctorLift.lift u) (FunctorLift.lift v)
    θ₁ = (copair-β₁ p q) ⁻¹ ∙ (FunctorLift.comparison u ∙
      ((r ◁ α) ∙ comp-assoc in₁ F r))
    θ₂ = (copair-β₂ p q) ⁻¹ ∙ (FunctorLift.comparison v ∙
      ((r ◁ β) ∙ comp-assoc in₂ F r))
    private
      module Triangle = RestrictionLift (r ∘ F) projection θ₁ θ₂
    over : FunctorOver projection r
    over = record { lift = F ; comparison = Triangle.lift }

    module Computation {A : CAT} {s : MAP A S} (j : FunctorOver s projection)
      (w : FunctorOver s r) (γ : (F ∘ FunctorLift.lift j) =₁ FunctorLift.lift w)
      (image : (Triangle.lift ▷ FunctorLift.lift j) =₂
        (FunctorLift.comparison j ⁻¹ ∙ (FunctorLift.comparison w ∙
          ((r ◁ γ) ∙ comp-assoc (FunctorLift.lift j) F r)))) where
      κ = FunctorLift.comparison j
      τ = FunctorLift.comparison w
      assoc = comp-assoc (FunctorLift.lift j) F r
      tail = τ ∙ ((r ◁ γ) ∙ assoc)
      abstract
        normalize : (κ ∙ ((κ ⁻¹ ∙ tail) ∙ assoc ⁻¹)) =₂ (τ ∙ (r ◁ γ))
        normalize = cancel-right assoc (τ ∙ (r ◁ γ)) ∙
          (isoComp-cong ((isoComp-assoc-at τ (r ◁ γ) assoc) ⁻¹) (idIso (assoc ⁻¹)) ∙
            (isoComp-cong (cancel-inverse κ tail) (idIso (assoc ⁻¹)) ∙
              (isoComp-assoc-at κ (κ ⁻¹ ∙ tail) (assoc ⁻¹)) ⁻¹))
        compatible : (τ ∙ (r ◁ γ)) =₂ FunctorLift.comparison (compose-over over j)
        compatible = (normalize ∙ isoComp-cong (idIso κ)
          (isoComp-cong image (idIso (assoc ⁻¹)))) ⁻¹
      comparison : FunctorOverIso (compose-over over j) w
      comparison = record { underlying = γ ; compatible = compatible }
    first-comparison = Computation.comparison first u α Triangle.left-image
    second-comparison = Computation.comparison second v β Triangle.right-image

  module Compare {E : CAT} {r : MAP E S} (u v : FunctorOver projection r)
    (first-comparison : FunctorOverIso (compose-over u first) (compose-over v first))
    (second-comparison : FunctorOverIso (compose-over u second) (compose-over v second)) where
    private
      module Lift = RestrictionLift (FunctorLift.lift u) (FunctorLift.lift v)
        (FunctorOverIso.underlying first-comparison) (FunctorOverIso.underlying second-comparison)
    abstract
      first-compatible : (FunctorLift.comparison (compose-over v first) ∙
        (r ◁ (Lift.lift ▷ in₁))) =₂ FunctorLift.comparison (compose-over u first)
      first-compatible = FunctorOverIso.compatible first-comparison ∙
        isoComp-cong (idIso (FunctorLift.comparison (compose-over v first)))
          (postWhisker r ◁ Lift.left-image)
      second-compatible : (FunctorLift.comparison (compose-over v second) ∙
        (r ◁ (Lift.lift ▷ in₂))) =₂ FunctorLift.comparison (compose-over u second)
      second-compatible = FunctorOverIso.compatible second-comparison ∙
        isoComp-cong (idIso (FunctorLift.comparison (compose-over v second)))
          (postWhisker r ◁ Lift.right-image)
      compatible : (FunctorLift.comparison v ∙ (r ◁ Lift.lift)) =₂ FunctorLift.comparison u
      compatible = coproduct-reflect-Iso₂
        (Restriction.comparison first u v Lift.lift first-compatible)
        (Restriction.comparison second u v Lift.lift second-compatible)
    comparison : FunctorOverIso u v
    comparison = record { underlying = Lift.lift ; compatible = compatible }


module Action {C D C′ D′ S : CAT}
  {p : MAP C S} {q : MAP D S} {p′ : MAP C′ S} {q′ : MAP D′ S}
  (u : FunctorOver p p′) (v : FunctorOver q q′) where
  private
    module Source = Sum p q
    module Target = Sum p′ q′
    module Chosen = Source.Copair (compose-over Target.first u) (compose-over Target.second v)
  open Chosen public using (over; first-comparison; second-comparison)

module Identity {C D S : CAT} (p : MAP C S) (q : MAP D S) where
  private
    module SumData = Sum p q
    module A = Action (identity-over p) (identity-over q)
  abstract
    first-comparison : FunctorOverIso (compose-over A.over SumData.first)
      (compose-over (identity-over SumData.projection) SumData.first)
    first-comparison = compose-iso-over (inverse-iso-over (left-unit-over SumData.first))
      (compose-iso-over (right-unit-over SumData.first) A.first-comparison)
    second-comparison : FunctorOverIso (compose-over A.over SumData.second)
      (compose-over (identity-over SumData.projection) SumData.second)
    second-comparison = compose-iso-over (inverse-iso-over (left-unit-over SumData.second))
      (compose-iso-over (right-unit-over SumData.second) A.second-comparison)
    comparison : FunctorOverIso A.over (identity-over SumData.projection)
    comparison = SumData.Compare.comparison A.over (identity-over SumData.projection)
      first-comparison second-comparison

module Composite {C D C′ D′ C″ D″ S : CAT}
  {p : MAP C S} {q : MAP D S} {p′ : MAP C′ S} {q′ : MAP D′ S}
  {p″ : MAP C″ S} {q″ : MAP D″ S}
  (u : FunctorOver p p′) (v : FunctorOver q q′)
  (u′ : FunctorOver p′ p″) (v′ : FunctorOver q′ q″) where
  private
    module Source = Sum p q
    module Middle = Sum p′ q′
    module Target = Sum p″ q″
    module A = Action u v
    module B = Action u′ v′
    module CompositeAction = Action (compose-over u′ u) (compose-over v′ v)
  abstract
    first-comparison : FunctorOverIso (compose-over (compose-over B.over A.over) Source.first)
      (compose-over CompositeAction.over Source.first)
    first-comparison = compose-iso-over (inverse-iso-over CompositeAction.first-comparison)
      (compose-iso-over (associator-over u u′ Target.first)
        (compose-iso-over (prewhisker-over u B.first-comparison)
          (compose-iso-over (inverse-iso-over (associator-over u Middle.first B.over))
            (compose-iso-over (postwhisker-over B.over A.first-comparison)
              (associator-over Source.first A.over B.over)))))
    second-comparison : FunctorOverIso (compose-over (compose-over B.over A.over) Source.second)
      (compose-over CompositeAction.over Source.second)
    second-comparison = compose-iso-over (inverse-iso-over CompositeAction.second-comparison)
      (compose-iso-over (associator-over v v′ Target.second)
        (compose-iso-over (prewhisker-over v B.second-comparison)
          (compose-iso-over (inverse-iso-over (associator-over v Middle.second B.over))
            (compose-iso-over (postwhisker-over B.over A.second-comparison)
              (associator-over Source.second A.over B.over)))))
    comparison : FunctorOverIso (compose-over B.over A.over) CompositeAction.over
    comparison = Source.Compare.comparison (compose-over B.over A.over) CompositeAction.over
      first-comparison second-comparison


module Identification {C D C′ D′ S : CAT}
  {p : MAP C S} {q : MAP D S} {p′ : MAP C′ S} {q′ : MAP D′ S}
  {u u′ : FunctorOver p p′} {v v′ : FunctorOver q q′}
  (α : FunctorOverIso u u′) (β : FunctorOverIso v v′) where
  private
    module Source = Sum p q
    module Target = Sum p′ q′
    module A = Action u v
    module B = Action u′ v′
  abstract
    comparison : FunctorOverIso A.over B.over
    comparison = Source.Compare.comparison A.over B.over
      (compose-iso-over (inverse-iso-over B.first-comparison)
        (compose-iso-over (postwhisker-over Target.first α) A.first-comparison))
      (compose-iso-over (inverse-iso-over B.second-comparison)
        (compose-iso-over (postwhisker-over Target.second β) A.second-comparison))
```
