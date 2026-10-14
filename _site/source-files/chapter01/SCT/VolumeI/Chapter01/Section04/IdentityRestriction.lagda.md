# Restriction of the chosen mapping identity

The identity comparison is the direct restriction of `mapId-β`. Its
restriction law uses the specified terminal comparison and the second
projection of the same product change. No anima hypothesis on either term
source is needed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.IdentityRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; preWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution
  using (module Coordinates; second-normalization; pair-pr₁-id-post)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase using (second-projection; change-parameter; module OverFirstFactor)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; unrestrict-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (module FrameChange)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (cancel-right; cancel-left; comp₌-unitˡ-One; comp₌-unitʳ-One)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Composition using (identity-map; mapId; mapId-β)
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase using (uncurry-identity; evaluation-over; evaluation-identity; evaluation⁼)
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction
open import SCT.VolumeI.Chapter01.Section04.EvaluationRestriction
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼; pair-pre)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares using (combine-pair)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)

private
  module IdentityCalculation {Γ : Context} {P Q C : CAT Γ} (σ : MAP Q P) where
    R = productMap σ (id C)
    TP = productMap (terminate P) (id C)
    TQ = productMap (terminate Q) (id C)
    TS = productMap (terminate P ∘ σ) (id C)
    γ = terminal-identification (terminate P ∘ σ) (terminate Q)
    K = productMap-first-comp {C = C} (terminate P) σ
    G = productMap-cong γ (const (id₌ (id C)))
    ψ = G ∙ K
    u = uncurry (mapId C)
    β = mapId-β C
    Aπ = comp-assoc R TP pr₂
    Au = comp-assoc R TP u
    BP = pair-β₂ (terminate P ∘ pr₁) (id C ∘ pr₂)
    BS = pair-β₂ ((terminate P ∘ σ) ∘ pr₁) (id C ∘ pr₂)
    BQ = pair-β₂ (terminate Q ∘ pr₁) (id C ∘ pr₂)
    λP = comp-unitˡ (pr₂ {C = P} {D = C})
    λQ = comp-unitˡ (pr₂ {C = Q} {D = C})
    ΠP = second-projection {D = C} (terminate P)
    ΠS = second-projection {D = C} (terminate P ∘ σ)
    ΠQ = second-projection {D = C} (terminate Q)
    Πσ = second-projection {D = C} σ
    ρP = uncurry-restrict (mapId C) (terminate P)
    ρS = uncurry-restrict (mapId C) (terminate P ∘ σ)
    ρQ = uncurry-restrict (mapId C) (terminate Q)
    ρσ = uncurry-restrict (identity-map {P = P} C) σ
    δ = const-pre (mapId C) σ
    Aterm = comp-assoc σ (terminate P) (mapId C)
    H = mapId C ◁ γ

    projection-iteration : (ΠS ∙ ((pr₂ ◁ K) ∙ Aπ)) =₂ (Πσ ∙ (ΠP ▷ R))
    projection-iteration =
      let S = Coordinates.second C (terminate P) σ
          raw = unrestrict-square pr₂ TP R TS K BP BS S
            (Coordinates.projection₂ C (terminate P) σ)
          first = comp₌-assoc λQ BS ((pr₂ ◁ K) ∙ Aπ)
          second = comp₌-cong (id₌ λQ) raw
          third = (comp₌-assoc λQ S (BP ▷ R)) ⁻¹
          normalize = comp₌-cong (id₌ λQ) (second-normalization C (terminate P) σ)
          fourth = comp₌-cong ((comp₌-assoc λQ
            (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)) (λP ▷ R)) ⁻¹ ∙ normalize) (id₌ (BP ▷ R))
          fifth = comp₌-assoc Πσ (λP ▷ R) (BP ▷ R)
          sixth = comp₌-cong (id₌ Πσ) ((preWhisker-comp₌ λP BP R) ⁻¹)
      in sixth ∙ (fifth ∙ (fourth ∙ (third ∙ (second ∙ first))))

    projection-substitution : (ΠQ ∙ (pr₂ ◁ G)) =₂ ΠS
    projection-substitution =
      let raw = unconst-sides₌ (productMap-cong-triangle₂ γ (const (id₌ (id C))))
          coordinate = preWhisker-id₌ (id C) pr₂ ∙
            (preWhisker pr₂ ◁ const-One (id₌ (id C)))
          normalized = comp₌-unitˡ-One BS ∙ comp₌-cong coordinate (id₌ BS) ∙ raw
          first = comp₌-assoc λQ BQ (pr₂ ◁ G)
          second = comp₌-cong (id₌ λQ) normalized
      in second ∙ first

    projection : (ΠQ ∙ (pr₂ ◁ ψ)) =₂ (Πσ ∙ restrict-triangle pr₂ TP ΠP R)
    projection = cancel-right Aπ
      (let first = comp₌-cong (comp₌-cong (id₌ ΠQ) (postWhisker-comp₌ pr₂ G K)) (id₌ Aπ)
           second = comp₌-cong ((comp₌-assoc ΠQ (pr₂ ◁ G) (pr₂ ◁ K)) ⁻¹) (id₌ Aπ)
           third = comp₌-cong (comp₌-cong projection-substitution (id₌ (pr₂ ◁ K))) (id₌ Aπ)
           fourth = comp₌-assoc ΠS (pr₂ ◁ K) Aπ
           last = (comp₌-assoc Πσ (restrict-triangle pr₂ TP ΠP R) Aπ) ⁻¹ ∙
             comp₌-cong (id₌ Πσ) ((inv-comp-right (ΠP ▷ R) Aπ) ⁻¹)
       in last ∙ (projection-iteration ∙ (fourth ∙ (third ∙ (second ∙ first)))))

    frame : ((ΠQ ∙ (β ▷ TQ)) ∙ ((u ◁ ψ) ∙ Au)) =₂
      (Πσ ∙ ((ΠP ∙ (β ▷ TP)) ▷ R))
    frame = FrameChange.compatible TP R TQ ψ u pr₂ pr₂ pr₂ β ΠP ΠQ
      (ΠP ∙ (β ▷ TP)) Πσ (ΠQ ∙ (β ▷ TQ)) (id₌ _) (id₌ _) projection

    uncurrying : (ρQ ∙ uncurry⁼ δ) =₂
      ((u ◁ ψ) ∙ (Au ∙ ((ρP ▷ R) ∙ ρσ)))
    uncurrying =
      let A = uncurry⁼ Aterm
          UG = uncurry⁼ H
          UK = u ◁ K
          VG = u ◁ G
          tail = (ρP ▷ R) ∙ ρσ
          substitution = unconst-sides₌ (uncurry-restrict-substitution (mapId C) γ)
          first = comp₌-cong (id₌ ρQ) (uncurry⁼-composition H Aterm)
          second = (comp₌-assoc ρQ UG A) ⁻¹
          third = comp₌-cong substitution (id₌ A)
          fourth = comp₌-assoc VG ρS A
          fifth = comp₌-cong (id₌ VG) (uncurry-restrict-iterated (mapId C) (terminate P) σ)
          sixth = (comp₌-assoc VG UK (Au ∙ tail)) ⁻¹
          seventh = comp₌-cong ((postWhisker-comp₌ u G K) ⁻¹) (id₌ (Au ∙ tail))
      in seventh ∙ (sixth ∙ (fifth ∙ (fourth ∙ (third ∙ (second ∙ first)))))

    restriction : (uncurry-identity Q C ∙ uncurry⁼ δ) =₂
      (Πσ ∙ ((uncurry-identity P C ▷ R) ∙ ρσ))
    restriction =
      let SQ = ΠQ ∙ (β ▷ TQ)
          SP = ΠP ∙ (β ▷ TP)
          tail = (ρP ▷ R) ∙ ρσ
          Uψ = (u ◁ ψ) ∙ Au
          normalizeQ = (comp₌-assoc ΠQ (β ▷ TQ) ρQ) ⁻¹
          normalizeP = (comp₌-assoc ΠP (β ▷ TP) ρP) ⁻¹
          first = comp₌-cong normalizeQ (id₌ (uncurry⁼ δ))
          second = comp₌-assoc SQ ρQ (uncurry⁼ δ)
          third = comp₌-cong (id₌ SQ) uncurrying
          fourth = comp₌-cong (id₌ SQ) ((comp₌-assoc (u ◁ ψ) Au tail) ⁻¹)
          fifth = (comp₌-assoc SQ Uψ tail) ⁻¹
          sixth = comp₌-cong frame (id₌ tail)
          seventh = comp₌-assoc Πσ (SP ▷ R) tail
          eighth = comp₌-cong (id₌ Πσ) ((comp₌-assoc (SP ▷ R) (ρP ▷ R) ρσ) ⁻¹)
          ninth = comp₌-cong (id₌ Πσ)
            (comp₌-cong ((preWhisker-comp₌ SP ρP R) ⁻¹) (id₌ ρσ))
          tenth = comp₌-cong (id₌ Πσ)
            (comp₌-cong (preWhisker R ◁ normalizeP ⁻¹) (id₌ ρσ))
      in tenth ∙ (ninth ∙ (eighth ∙ (seventh ∙ (sixth ∙
        (fifth ∙ (fourth ∙ (third ∙ (second ∙ first))))))))

module _ {Γ : Context} {P Q C : CAT Γ} where
  uncurry-identity-restrict : (σ : MAP Q P)
    → (uncurry-identity Q C ∙ uncurry⁼ (const-pre (mapId C) σ)) =₂
        (second-projection σ ∙ ((uncurry-identity P C ▷ productMap σ (id C)) ∙
          uncurry-restrict (identity-map {P = P} C) σ))
  uncurry-identity-restrict σ = IdentityCalculation.restriction σ
```
The relative law compares the actual route through the identity at the
changed source with the route through `evaluation-restrict-over` and the
identity at the original source. The right route supplies its compatibility
over the base; transport along the proved equality gives that compatibility
for the left route. No equality of higher proof fields is asserted.

```agda
module IdentityUnderRestriction {Γ : Context} {P Q C : CAT Γ} (σ : MAP Q P) where
  private
    R = productMap σ (id C)
    Jp = identity-map {P = P} C
    Jq = identity-map {P = Q} C
    δ = const-pre (mapId C) σ
    v = uncurry (Jp ∘ σ)
    vp = uncurry Jp
    vq = uncurry Jq
    qp = uncurry-identity P C
    qq = uncurry-identity Q C
    qδ = uncurry⁼ δ
    qt = qq ∙ qδ
    ρ = uncurry-restrict Jp σ
    E = evaluation-restrict Jp σ
    Ip = IdentificationOver.identification (evaluation-identity P C)
    Iq = IdentificationOver.identification (evaluation-identity Q C)
    B₁ = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
    B₂ = pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
    λv = comp-unitˡ v
    λq = comp-unitˡ (pr₂ {C = Q} {D = C})
    pre = pair-pre pr₁ vp R
    base = productMap-pair σ (id C) pr₁ v
    out = pair⁼ B₁ (id₌ (vp ∘ R)) ∙ pre
    input = pair⁼ (id₌ (σ ∘ pr₁)) (ρ ∙ λv) ∙ base
    finish = B₂ ∙ (qp ▷ R)
    T = pair⁼ (id₌ (σ ∘ pr₁)) finish

  source = comp-over-map σ (change-parameter σ) (evaluation-over (Jp ∘ σ))
  target = change-parameter {D = C} σ

  left-identification : FunctorOverBase.functor source =₁ FunctorOverBase.functor target
  left-identification = comp-unitʳ R ∙ ((R ◁ Iq) ∙ (R ◁ evaluation⁼ δ))

  right : IdentificationOver {A = One {Γ}} source target
  right = comp-identification-over
    (identification-over (comp-unitˡ R) (identification-over-unitˡ target))
    (comp-identification-over
      (identification-over (Ip ▷ R)
        (identification-over-pre target (IdentificationOver.over (evaluation-identity P C))))
      (evaluation-restrict-over Jp σ))

  private
    left-normalization : left-identification =₂
      (pair⁼ (id₌ (σ ∘ pr₁)) (id C ◁ qt) ∙ base)
    left-normalization =
      let η = OverFirstFactor.pair-pr₁-id Q C
          bq = pair⁼ (id₌ pr₁) qq
          bδ = pair⁼ (id₌ pr₁) qδ
          action = pair⁼-cong (const-One (id₌ pr₁)) (id₌ qδ)
          inner = comp₌-cong (id₌ η) ((pair⁼-fixed-first-comp-One pr₁ qq qδ) ⁻¹) ∙
            (comp₌-assoc η bq bδ ∙ comp₌-cong (id₌ Iq) action)
          first = comp₌-cong (id₌ (comp-unitʳ R)) ((postWhisker-comp₌ R Iq (evaluation⁼ δ)) ⁻¹)
          second = comp₌-cong (id₌ (comp-unitʳ R)) (postWhisker R ◁ inner)
      in pair-pr₁-id-post σ qt ∙ (second ∙ first)

    finish-normalization : (T ∙ out) =₂
      (pair⁼ B₁ finish ∙ pre)
    finish-normalization =
      comp₌-cong (pair⁼-cong (comp₌-unitˡ-One B₁) (comp₌-unitʳ-One finish)) (id₌ pre) ∙
        combine-pair (id₌ (σ ∘ pr₁)) finish B₁ (id₌ (vp ∘ R)) pre

    right-normalization : IdentificationOver.identification right =₂
      (pair⁼ (id₌ (σ ∘ pr₁)) (finish ∙ (ρ ∙ λv)) ∙ base)
    right-normalization =
      let first = (comp₌-assoc (comp-unitˡ R) (Ip ▷ R) E) ⁻¹
          second = comp₌-cong (OverFirstFactor.pair-pr₁-id-pre P
            (σ ∘ pr₁) (id C ∘ pr₂) qp) (id₌ E)
          third = comp₌-cong (finish-normalization ⁻¹) (id₌ E)
          fourth = comp₌-assoc T out (out ⁻¹ ∙ input)
          fifth = comp₌-cong (id₌ T) (comp-inv-left out input)
          sixth = combine-pair (id₌ (σ ∘ pr₁)) finish
            (id₌ (σ ∘ pr₁)) (ρ ∙ λv) base
          seventh = comp₌-cong
            (pair⁼-cong (comp₌-unitˡ-One (id₌ (σ ∘ pr₁))) (id₌ (finish ∙ (ρ ∙ λv)))) (id₌ base)
      in seventh ∙ (sixth ∙ (fifth ∙ (fourth ∙ (third ∙ (second ∙ first)))))

    second-coordinate : (id C ◁ qt) =₂ (finish ∙ (ρ ∙ λv))
    second-coordinate = cancel-left λq
      (let first = postWhisker-id-One qt
           second = comp₌-cong (uncurry-identity-restrict σ) (id₌ λv)
           third = comp₌-assoc (second-projection σ) ((qp ▷ R) ∙ ρ) λv
           fourth = comp₌-cong (id₌ (second-projection σ)) (comp₌-assoc (qp ▷ R) ρ λv)
           fifth = comp₌-assoc λq B₂ ((qp ▷ R) ∙ (ρ ∙ λv))
           sixth = comp₌-cong (id₌ λq) ((comp₌-assoc B₂ (qp ▷ R) (ρ ∙ λv)) ⁻¹)
       in sixth ∙ (fifth ∙ (fourth ∙ (third ∙ (second ∙ first)))))

  restriction : left-identification =₂ IdentificationOver.identification right
  restriction = right-normalization ⁻¹ ∙
    (comp₌-cong (pair⁼-cong (id₌ (id₌ (σ ∘ pr₁))) second-coordinate) (id₌ base) ∙
      left-normalization)

  left : IdentificationOver {A = One {Γ}} source target
  left = identification-over left-identification
    (replace-edges₌ (postWhisker pr₁ ◁ restriction ⁻¹) (id₌ _)
      (IdentificationOver.over right))

  normalized-change : (R ∘ FunctorOverBase.functor (evaluation-over Jq)) =₁
    (FunctorOverBase.functor (evaluation-over Jp) ∘ R)
  normalized-change = E ∙ (R ◁ evaluation⁼ δ) ⁻¹

  unit-square : (R ∘ id (Q × C)) =₁ (id (P × C) ∘ R)
  unit-square = (comp-unitˡ R) ⁻¹ ∙ comp-unitʳ R

  natural : ((Ip ▷ R) ∙ normalized-change) =₂ (unit-square ∙ (R ◁ Iq))
  natural =
    let action : (R ∘ FunctorOverBase.functor (evaluation-over (Jp ∘ σ))) =₁
          (R ∘ FunctorOverBase.functor (evaluation-over Jq))
        action = R ◁ evaluation⁼ δ
        ep = Ip ▷ R
        eq = R ◁ Iq
        λR = comp-unitˡ R
        ρR = comp-unitʳ R
        left-normalize = comp₌-cong (id₌ λR)
          (comp₌-cong (id₌ ep) (inv-comp-right E action) ∙
            comp₌-assoc ep (E ∙ action ⁻¹) action)
        right-normalize = comp₌-cong (comp-inv-left λR ρR) (id₌ (eq ∙ action)) ∙
          ((comp₌-assoc λR unit-square (eq ∙ action)) ⁻¹ ∙
            comp₌-cong (id₌ λR) (comp₌-assoc unit-square eq action))
    in cancel-right action (cancel-left λR
      (right-normalize ⁻¹ ∙ (restriction ⁻¹ ∙ left-normalize)))
```