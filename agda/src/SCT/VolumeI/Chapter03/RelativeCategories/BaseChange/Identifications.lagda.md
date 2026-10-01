# Base change of native triangles

Pulling back a functor over the base uses its given triangle as part of
the new pullback cone. Identifications of such functors induce
identifications over the new base. This action is constructed on the
whole anima of relative identifications, retaining its triangle witness
when a lifted identification is used in a further calculation.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle; module Compare; module Reflect)
open PN vocabulary terminal products productLaws composition vertical whiskering using (pre-square-projection; cancel-right)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; conePre-id; conePre-assoc; coneIso-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action; compose-action)
import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChangeComparisonFamilies as ComparisonFamilies
import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChangeHigherIdentifications as Higher
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding 𝒯 M ℱ P
  using () renaming (module Encoding to RelativeEncoding)

module Change {S T : CAT} (p : MAP S T) where
  cone : {C D : CAT} {f : MAP C T} {g : MAP D T} →
    FunctorOver f g → Cone g p (Pullback f p)
  cone {f = f} {g} u = record
    { left = FunctorLift.lift u ∘ pullback₁ ; right = pullback₂
    ; match = pullbackMatch {f = f} {p} ∙
        ((FunctorLift.comparison u ▷ pullback₁) ∙
          (comp-assoc pullback₁ (FunctorLift.lift u) g) ⁻¹) }

  functor : {C D : CAT} {f : MAP C T} {g : MAP D T} →
    FunctorOver f g → FunctorOver (pullback₂ {f = f} {p}) (pullback₂ {f = g} {p})
  functor u = lift-triangle (cone u)

  module Identification {C D : CAT} {f : MAP C T} {g : MAP D T}
    {u v : FunctorOver f g} (Φ : FunctorOverIso u v) where
    module Encoded = ComparisonFamilies.Change 𝒯 M ℱ P p u v
      using (comparison)
    h : MAP C D
    h = FunctorLift.lift u
    k : MAP C D
    k = FunctorLift.lift v
    r : MAP (Pullback f p) C
    r = pullback₁
    θ : (g ∘ h) =₁ f
    θ = FunctorLift.comparison u
    ψ : (g ∘ k) =₁ f
    ψ = FunctorLift.comparison v
    α : h =₁ k
    α = FunctorOverIso.underlying Φ
    source : (g ∘ (h ∘ r)) =₁ (f ∘ r)
    source = (θ ▷ r) ∙ (comp-assoc r h g) ⁻¹
    target : (g ∘ (k ∘ r)) =₁ (f ∘ r)
    target = (ψ ▷ r) ∙ (comp-assoc r k g) ⁻¹

    -- These calculations describe the restricted input triangle. The
    -- comparison below is lifted through the universal comparison family;
    -- no agreement with a separately chosen pointwise lift is asserted.
    abstract
      restricted-square : (target ∙ (g ◁ (α ▷ r))) =₂ source
      restricted-square = isoComp-unitˡ-at source ∙
        (isoComp-cong (preWhisker-idIso f r) (idIso source) ∙
          pre-square-projection g α (idIso f) θ ψ r
            ((isoComp-unitˡ-at θ) ⁻¹ ∙ FunctorOverIso.compatible Φ))

      matching : (Cone.match (cone v) ∙ (g ◁ (α ▷ r))) =₂ Cone.match (cone u)
      matching = isoComp-cong (idIso (pullbackMatch {f = f} {p})) restricted-square ∙
        isoComp-assoc-at (pullbackMatch {f = f} {p}) target (g ◁ (α ▷ r))

    opaque
      comparison : FunctorOverIso (functor u) (functor v)
      comparison = Encoded.comparison Φ

    opaque
      unfolding comparison
      comparison-underlying : FunctorOverIso.underlying comparison =₂
        FunctorOverIso.underlying (Encoded.comparison Φ)
      comparison-underlying = idIso _

  opaque
    unfolding Identification.comparison
    higher-identification-image : {C D : CAT} {f : MAP C T} {g : MAP D T}
      {u v : FunctorOver f g} {Φ Ψ : FunctorOverIso u v} → FunctorOverIso₂ Φ Ψ →
      FunctorOverIso₂ (Identification.comparison Φ) (Identification.comparison Ψ)
    higher-identification-image {u = u} {v} Ξ = Higher.Identification.congruence 𝒯 M ℱ P p u v Ξ

  opaque
    encoded-identification-image : {C D : CAT} {f : MAP C T} {g : MAP D T}
      {u v : FunctorOver f g} {Φ Ψ : FunctorOverIso u v} →
      RelativeEncoding.point u v Φ =₁ RelativeEncoding.point u v Ψ →
      FunctorOverIso.underlying (Identification.comparison Φ) =₂
      FunctorOverIso.underlying (Identification.comparison Ψ)
    encoded-identification-image {u = u} {v} {Φ} {Ψ} δ =
      (Identification.comparison-underlying Ψ) ⁻¹ ∙
      ((ComparisonFamilies.Change.functor 𝒯 M ℱ P p u v ◁ δ) ∙
        Identification.comparison-underlying Φ)

  module Identity {C : CAT} (f : MAP C T) where
    r : MAP (Pullback f p) C
    r = pullback₁
    q : MAP (Pullback f p) S
    q = pullback₂
    s : Cone f p (Pullback f p)
    s = cone (identity-over f)
    τ : (f ∘ r) =₁ (p ∘ q)
    τ = pullbackMatch

    abstract
      matching : Cone.match s =₂ (τ ∙ (f ◁ comp-unitˡ r))
      matching = isoComp-cong (idIso τ)
        (cancel-right (comp-assoc r (id C) f) (f ◁ comp-unitˡ r) ∙
          isoComp-cong (triangle-whiskered r f) (idIso ((comp-assoc r (id C) f) ⁻¹)))

    cones : ConeIso s (pullbackCone f p)
    cones = record { leftIso = comp-unitˡ r ; rightIso = idIso q
      ; compatible = isoComp-cong ((postWhisker-idIso p q) ⁻¹) (idIso (Cone.match s)) ∙
            ((isoComp-unitˡ-at (Cone.match s)) ⁻¹ ∙ matching ⁻¹) }

    compared : ConeIso (conePre (pullbackLift s) (pullbackCone f p))
      (conePre (id (Pullback f p)) (pullbackCone f p))
    compared = coneIso-compose (coneIso-inverse (conePre-id (pullbackCone f p)))
      (coneIso-compose cones (pullbackLift-β s))

    abstract
      right-comparison : (comp-unitʳ q ∙ ConeIso.rightIso compared) =₂ pullbackLift-β₂ s
      right-comparison = isoComp-unitˡ-at (pullbackLift-β₂ s) ∙
        cancel-inverse (comp-unitʳ q) (idIso q ∙ pullbackLift-β₂ s)

      comparison : FunctorOverIso (functor (identity-over f)) (identity-over q)
      comparison = Reflect.comparison (functor (identity-over f)) (identity-over q) compared right-comparison

  module Composite {B C D : CAT} {f : MAP B T} {g : MAP C T} {h : MAP D T}
    (u : FunctorOver f g) (v : FunctorOver g h) where
    nu : MAP (Pullback f p) (Pullback g p)
    nu = FunctorLift.lift (functor u)
    nv : MAP (Pullback g p) (Pullback h p)
    nv = FunctorLift.lift (functor v)
    qf : MAP (Pullback f p) S
    qf = pullback₂
    qg : MAP (Pullback g p) S
    qg = pullback₂
    qh : MAP (Pullback h p) S
    qh = pullback₂
    βu : (qg ∘ nu) =₁ qf
    βu = pullbackLift-β₂ (cone u)
    βv : (qh ∘ nv) =₁ qg
    βv = pullbackLift-β₂ (cone v)
    βvu : (qh ∘ FunctorLift.lift (functor (compose-over v u))) =₁ qf
    βvu = pullbackLift-β₂ (cone (compose-over v u))
    tail : (qh ∘ (nv ∘ nu)) =₁ (qg ∘ nu)
    tail = (βv ▷ nu) ∙ (comp-assoc nu nv qh) ⁻¹

    compared : ConeIso (conePre (nv ∘ nu) (pullbackCone h p))
      (conePre (FunctorLift.lift (functor (compose-over v u))) (pullbackCone h p))
    compared = coneIso-compose (coneIso-inverse (pullbackLift-β (cone (compose-over v u))))
      (coneIso-compose (coneIso-inverse (compose-action p u v (pullbackCone f p)))
        (coneIso-compose (Action.map-iso p v (pullbackLift-β (cone u)))
          (coneIso-compose (Action.restriction p v nu (pullbackCone g p))
            (coneIso-compose (coneIso-pre nu (pullbackLift-β (cone v)))
              (coneIso-inverse (conePre-assoc nu nv (pullbackCone h p)))))))

    abstract
      right-comparison : (βvu ∙ ConeIso.rightIso compared) =₂ (βu ∙ tail)
      right-comparison = isoComp-cong (idIso βu) (isoComp-unitˡ-at tail) ∙
        (isoComp-unitˡ-at (βu ∙ (idIso (qg ∘ nu) ∙ tail)) ∙
          (isoComp-cong (inverse-identity qf) (idIso (βu ∙ (idIso (qg ∘ nu) ∙ tail))) ∙
            cancel-inverse βvu ((idIso qf) ⁻¹ ∙ (βu ∙ (idIso (qg ∘ nu) ∙ tail)))))

    module Reflected = Reflect (compose-over (functor v) (functor u)) (functor (compose-over v u))
      compared right-comparison using (comparison; induced-cone; cone-computation; triangle-computation)

    abstract
      comparison : FunctorOverIso (compose-over (functor v) (functor u)) (functor (compose-over v u))
      comparison = Reflected.comparison

      cone-computation : ConeIso₂
        (Reflected.induced-cone (FunctorOverIso.underlying comparison)) compared
      cone-computation = Reflected.cone-computation

      triangle-computation : FunctorOverIso.compatible comparison =₃
        (right-comparison ∙ isoComp-cong (idIso βvu) (ConeIso₂.rightId cone-computation))
      triangle-computation = Reflected.triangle-computation
```
