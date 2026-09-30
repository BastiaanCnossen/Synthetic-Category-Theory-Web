# Interval diagrams of transformations over a base

Uncurrying a transformation over the base gives a functor from the
parameter category times the interval over that base. Both endpoint
identifications are identifications of relative functors, with their
complete triangle compatibility.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.RelativeCategories.MorphismDiagrams
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
  using (FunctorOverIso)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedExpressionComparisons as Uncurried

private
  abstract
    drop-last : {Γ C : CAT} {x₀ x₁ x₂ x₃ : MAP Γ C}
      (a : x₂ =₁ x₃) (b : x₁ =₁ x₂) (d : x₀ =₁ x₁) →
      ((a ∙ (b ∙ d)) ∙ d ⁻¹) =₂ (a ∙ b)
    drop-last a b d = cancel-right d (a ∙ b) ∙
      isoComp-cong ((isoComp-assoc-at a b d) ⁻¹) (idIso (d ⁻¹))

    drop-post-tail : {Γ C : CAT} {x₀ x₁ x₂ x₃ x₄ x₅ : MAP Γ C}
      (a : x₄ =₁ x₅) (b : x₃ =₁ x₄) (d : x₂ =₁ x₃) (e : x₁ =₁ x₂) (h : x₀ =₁ x₁) →
      ((a ∙ (b ∙ (d ∙ (e ∙ h)))) ∙ h ⁻¹) =₂ ((a ∙ b) ∙ (d ∙ e))
    drop-post-tail a b d e h = (isoComp-assoc-at a b (d ∙ e)) ⁻¹ ∙
      drop-last a (b ∙ (d ∙ e)) h ∙
      isoComp-cong
        (isoComp-cong (idIso a)
          ((isoComp-assoc-at b (d ∙ e) h) ⁻¹ ∙
            isoComp-cong (idIso b) ((isoComp-assoc-at d e h) ⁻¹)))
        (idIso (h ⁻¹))

    cancel-two : {Γ C : CAT} {x₀ x₁ x₂ x₃ : MAP Γ C}
      (a : x₂ =₁ x₃) (b : x₁ =₁ x₂) (d : x₀ =₁ x₁) →
      (((a ∙ (b ∙ d)) ∙ d ⁻¹) ∙ b ⁻¹) =₂ a
    cancel-two a b d = cancel-right b a ∙ isoComp-cong (drop-last a b d) (idIso (b ⁻¹))

module Diagram {C D B : CAT} {p : MAP C B} {q : MAP D B} {u v : FunctorOver p q}
  (α : Over.MorphismOver p q u v) where
  private
    module U = FunctorLift u
    module V = FunctorLift v
    module F = Over.MorphismOver α
    module A = MorphismExpression F.underlying
    module Compared = Uncurried.UncurryComparison 𝒯 M ℱ P I E F.over-base
  H = funUncurry A.arrow
  K = p ∘ pr₁ {C = C} {D = [1]}
  β = funCurry-β K
  σ = Compared.underlying
  θ = funPost-uncurry q A.arrow
  ρ = (β ∙ σ) ∙ θ ⁻¹

  family : FunctorOver K q
  family = record { lift = H ; comparison = ρ }

  module Endpoint (z : Obj-abs [1]) (w : FunctorOver p q)
    (frame : (evaluate z ∘ A.arrow) =₁ FunctorLift.lift w)
    (compatible : (((identity-boundary z p ∙ evaluate-curry z K) ∙
      (evaluate z ◁ ExpressionIso.comparison F.over-base))) =₂
      (FunctorLift.comparison w ∙ post-boundary z q A.arrow frame)) where
    private module W = FunctorLift w
    i = insert {X = C} z
    boundary = frame ∙ (evaluate-uncurry z A.arrow) ⁻¹
    insertion : FunctorOver p K
    insertion = record { lift = i ; comparison = identity-boundary z p }
    βi = β ▷ i
    σi = σ ▷ i
    θi = θ ▷ i
    edge = q ◁ boundary
    associator = comp-assoc i H q
    Q₀ = evaluate-uncurry z (funPost q ∘ A.arrow)
    Q₁ = evaluate-uncurry z (funCurry K)
    end = identity-boundary z p
    module Unc = Compared.Endpoint z
      (W.comparison ∙ post-boundary z q A.arrow frame)
      (end ∙ evaluate-curry z K) compatible

    abstract
      before : ((W.comparison ∙ post-boundary z q A.arrow frame) ∙ Q₀ ⁻¹) =₂
        ((W.comparison ∙ edge) ∙ (associator ∙ θi))
      before = drop-post-tail W.comparison edge associator θi Q₀

      after : ((end ∙ evaluate-curry z K) ∙ Q₁ ⁻¹) =₂ (end ∙ βi)
      after = drop-last end βi Q₁

      square : (end ∙ (βi ∙ σi)) =₂ ((W.comparison ∙ edge) ∙ (associator ∙ θi))
      square = before ∙ Unc.comparison ∙ isoComp-cong (after ⁻¹) (idIso σi) ∙
        (isoComp-assoc-at end βi σi) ⁻¹

      family-frame : (ρ ▷ i) =₂ ((βi ∙ σi) ∙ θi ⁻¹)
      family-frame = isoComp-cong (preWhisker-isoComp-at β σ i) (pre-inverse θ i) ∙
        preWhisker-isoComp-at (β ∙ σ) (θ ⁻¹) i

      source-frame : FunctorLift.comparison (compose-over family insertion) =₂ (W.comparison ∙ edge)
      source-frame = cancel-two (W.comparison ∙ edge) associator θi ∙
        isoComp-cong (isoComp-cong square (idIso (θi ⁻¹))) (idIso (associator ⁻¹)) ∙
        isoComp-cong ((isoComp-assoc-at end (βi ∙ σi) (θi ⁻¹)) ⁻¹) (idIso (associator ⁻¹)) ∙
        isoComp-cong (isoComp-cong (idIso end) family-frame) (idIso (associator ⁻¹)) ∙
        (isoComp-assoc-at end (ρ ▷ i) (associator ⁻¹)) ⁻¹

      comparison : FunctorOverIso (compose-over family insertion) w
      comparison = record { underlying = boundary ; compatible = source-frame ⁻¹ }

      underlying-comparison : FunctorOverIso.underlying comparison =₂ boundary
      underlying-comparison = idIso boundary

  module Source = Endpoint zero u A.source-frame (ExpressionIso.source-compatible F.over-base)
  module Target = Endpoint one v A.target-frame (ExpressionIso.target-compatible F.over-base)
```
