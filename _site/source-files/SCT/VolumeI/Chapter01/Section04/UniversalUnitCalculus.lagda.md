# Calculus for restricting the universal unit comparisons

The unit comparisons are chosen on a mapping anima and then restricted
along a parameter map. We compare those restrictions with the unit routes
lifted directly at the new parameter. The identity comparison and every
composition comparison used here are the previously specified ones.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as Internal
import SCT.VolumeI.Chapter01.Section04.UniversalCoherence as Universal
import SCT.VolumeI.Chapter01.Section04.RetainedIdentityParameterChange as IdentityChange
import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section04.ParameterSquareUnits as ParameterSquareUnits
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section04.UniversalUnitCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open Internal 𝒯 M
open Universal 𝒯 M using
  (module NormalizedChange; module NormalizedComposition; module UnitRestriction;
   paste-natural; unchanged-parameter-square)
open IdentityChange 𝒯 M using (retained-identity-parameter-change)
open ParameterSquarePasting 𝒯 using (paste)
open ParameterSquareUnits 𝒯 using (unit-square; unit-square-cancel; paste-unitˡ; paste-unitʳ)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (hcomp-idInner; hcomp-idOuter)

opaque
  pre-three : {W X Y : CAT} (r : MAP W X) {a b c d : MAP X Y}
    (γ : c =₁ d) (β : b =₁ c) (α : a =₁ b)
    → ((γ ∙ (β ∙ α)) ▷ r) =₂ ((γ ▷ r) ∙ ((β ▷ r) ∙ (α ▷ r)))
  pre-three r γ β α = isoComp-cong (idIso (γ ▷ r)) (preWhisker-isoComp-at β α r) ∙
    preWhisker-isoComp-at γ (β ∙ α) r

  post-three : {X Y Z : CAT} (r : MAP Y Z) {a b c d : MAP X Y}
    (γ : c =₁ d) (β : b =₁ c) (α : a =₁ b)
    → (r ◁ (γ ∙ (β ∙ α))) =₂ ((r ◁ γ) ∙ ((r ◁ β) ∙ (r ◁ α)))
  post-three r γ β α = isoComp-cong (idIso (r ◁ γ)) (postWhisker-isoComp-at r β α) ∙
    postWhisker-isoComp-at r γ (β ∙ α)

module Identity {P Q : CAT} (σ : MAP Q P) (C : CAT) where
  module N = NormalizedChange {C = C} {D = C} σ
  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q
  s = productMap σ (id C)
  J = identityTerm {Γ = P} C
  δ = const-pre (mapId C) σ
  η = N.image δ
  κ = N.change J δ
  u = unit-square s
  eP = RP.retained-identity C ▷ s
  eQ = s ◁ RQ.retained-identity C

  opaque
    natural : (eP ∙ κ) =₂ (u ∙ eQ)
    natural =
      let λs = comp-unitˡ s
          ρs = comp-unitʳ s
          L = eP ∙ κ
          R = u ∙ eQ
          normalize-left = isoComp-cong (idIso λs)
            (isoComp-cong (idIso eP) (N.change-cancel J δ) ∙ isoComp-assoc-at eP κ η)
          normalize-right = isoComp-cong (unit-square-cancel s) (idIso (eQ ∙ η)) ∙
            ((isoComp-assoc-at λs u (eQ ∙ η)) ⁻¹ ∙
              isoComp-cong (idIso λs) (isoComp-assoc-at u eQ η))
      in cancel-right-reflect η
        (cancel-left-reflect λs
          (normalize-right ⁻¹ ∙
            ((retained-identity-parameter-change {C = C} σ) ⁻¹ ∙ normalize-left)))

module UnitChange {P Q C D : CAT} (σ : MAP Q P)
  (f : MAP P (Map C D)) {f′ : MAP Q (Map C D)} (Lf : (f ∘ σ) =₁ f′) where
  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q
  module N (A B : CAT) = NormalizedChange {C = A} {D = B} σ
  module NC = NormalizedComposition σ
  sC = productMap σ (id C)
  sD = productMap σ (id D)
  F = RP.retained f
  F′ = RQ.retained f′
  κf = N.change C D f Lf

  left-boundary = composeTerm-evaluate (identityTerm D) f σ (const-pre (mapId D) σ) Lf
  right-boundary = composeTerm-evaluate f (identityTerm C) σ Lf (const-pre (mapId C) σ)
  κleft = N.change C D (composeTerm (identityTerm D) f) left-boundary
  κright = N.change C D (composeTerm f (identityTerm C)) right-boundary

  opaque
    left-route : NC.BasicSquare (identityTerm D) f
      → (κf ∙ (sD ◁ RQ.left-unit-route f′)) =₂ ((RP.left-unit-route f ▷ sC) ∙ κleft)
    left-route basic =
      let module I = Identity σ D
          cP = RP.retained-compose (identityTerm D) f
          cQ = RQ.retained-compose (identityTerm D) f′
          eP = RP.retained-identity D ▷ F
          eQ = RQ.retained-identity D ▷ F′
          uP = comp-unitˡ F
          uQ = comp-unitˡ F′
          p : (sD ∘ (RQ.retained (identityTerm D) ∘ F′)) =₁
            ((RP.retained (identityTerm D) ∘ F) ∘ sC)
          p = paste I.κ κf
          pUnit : (sD ∘ (id (Q × D) ∘ F′)) =₁ ((id (P × D) ∘ F) ∘ sC)
          pUnit = paste I.u κf
          cSquare : ((cP ▷ sC) ∙ κleft) =₂ (p ∙ (sD ◁ cQ))
          cSquare = (NC.normalize (identityTerm D) f (const-pre (mapId D) σ) Lf basic) ⁻¹
          eSquare : ((eP ▷ sC) ∙ p) =₂ (pUnit ∙ (sD ◁ eQ))
          eSquare = isoComp-cong (idIso pUnit) (postWhisker sD ◁ hcomp-idInner (RQ.retained-identity D) F′) ∙
            (paste-natural
              {f = F′} {f′ = F′} {g = RQ.retained (identityTerm D)} {g′ = id (Q × D)}
              {F = F} {F′ = F} {G = RP.retained (identityTerm D)} {G′ = id (P × D)}
              {x₀ = sC} {x₁ = sD} {x₂ = sD}
              I.κ I.u κf κf (RQ.retained-identity D) (idIso F′)
              (RP.retained-identity D) (idIso F) I.natural (unchanged-parameter-square κf) ∙
              isoComp-cong (preWhisker sC ◁ (hcomp-idInner (RP.retained-identity D) F) ⁻¹) (idIso p))
          two = paste-squares (sD ◁ cQ) (cP ▷ sC) (sD ◁ eQ) (eP ▷ sC)
            κleft p pUnit cSquare eSquare
          three = paste-squares ((sD ◁ eQ) ∙ (sD ◁ cQ)) ((eP ▷ sC) ∙ (cP ▷ sC))
            (sD ◁ uQ) (uP ▷ sC) κleft pUnit κf two (paste-unitˡ κf)
      in isoComp-cong ((pre-three sC uP eP cP) ⁻¹) (idIso κleft) ∙
        (three ⁻¹ ∙ isoComp-cong (idIso κf) (post-three sD uQ eQ cQ))

    right-route : NC.BasicSquare f (identityTerm C)
      → (κf ∙ (sD ◁ RQ.right-unit-route f′)) =₂ ((RP.right-unit-route f ▷ sC) ∙ κright)
    right-route basic =
      let module I = Identity σ C
          cP = RP.retained-compose f (identityTerm C)
          cQ = RQ.retained-compose f′ (identityTerm C)
          eP = F ◁ RP.retained-identity C
          eQ = F′ ◁ RQ.retained-identity C
          uP = comp-unitʳ F
          uQ = comp-unitʳ F′
          p : (sD ∘ (F′ ∘ RQ.retained (identityTerm C))) =₁
            ((F ∘ RP.retained (identityTerm C)) ∘ sC)
          p = paste κf I.κ
          pUnit : (sD ∘ (F′ ∘ id (Q × C))) =₁ ((F ∘ id (P × C)) ∘ sC)
          pUnit = paste κf I.u
          cSquare : ((cP ▷ sC) ∙ κright) =₂ (p ∙ (sD ◁ cQ))
          cSquare = (NC.normalize f (identityTerm C) Lf (const-pre (mapId C) σ) basic) ⁻¹
          eSquare : ((eP ▷ sC) ∙ p) =₂ (pUnit ∙ (sD ◁ eQ))
          eSquare = isoComp-cong (idIso pUnit) (postWhisker sD ◁ hcomp-idOuter F′ (RQ.retained-identity C)) ∙
            (paste-natural
              {f = RQ.retained (identityTerm C)} {f′ = id (Q × C)} {g = F′} {g′ = F′}
              {F = RP.retained (identityTerm C)} {F′ = id (P × C)} {G = F} {G′ = F}
              {x₀ = sC} {x₁ = sC} {x₂ = sD}
              κf κf I.κ I.u (idIso F′) (RQ.retained-identity C)
              (idIso F) (RP.retained-identity C) (unchanged-parameter-square κf) I.natural ∙
              isoComp-cong (preWhisker sC ◁ (hcomp-idOuter F (RP.retained-identity C)) ⁻¹) (idIso p))
          two = paste-squares (sD ◁ cQ) (cP ▷ sC) (sD ◁ eQ) (eP ▷ sC)
            κright p pUnit cSquare eSquare
          three = paste-squares ((sD ◁ eQ) ∙ (sD ◁ cQ)) ((eP ▷ sC) ∙ (cP ▷ sC))
            (sD ◁ uQ) (uP ▷ sC) κright pUnit κf two (paste-unitʳ κf)
      in isoComp-cong ((pre-three sC uP eP cP) ⁻¹) (idIso κright) ∙
        (three ⁻¹ ∙ isoComp-cong (idIso κf) (post-three sD uQ eQ cQ))
```


