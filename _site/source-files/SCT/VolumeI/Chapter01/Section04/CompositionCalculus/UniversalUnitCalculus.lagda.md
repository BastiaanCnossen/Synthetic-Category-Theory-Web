# Calculus for restricting the universal unit comparisons

The unit comparisons are chosen on a mapping anima and then restricted
along a parameter map. We compare those restrictions with the unit routes
lifted directly at the new parameter. The identity comparison and every
composition comparison used here are the previously specified ones.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as Internal
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalCoherence as Universal
import SCT.VolumeI.Chapter01.Section04.Substitution.RetainedIdentityParameterChange as IdentityChange
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquareNaturality as ParameterSquareNaturality
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquareUnits as ParameterSquareUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits

module SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalUnitCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open Internal 𝒯 M
open Universal 𝒯 M using
  (module NormalizedChange; module NormalizedComposition; module UnitRestriction)
open IdentityChange 𝒯 M using (retained-identity-parameter-change)
open ParameterSquarePasting 𝒯 using (paste)
open ParameterSquareNaturality 𝒯 using (paste-natural-outer; paste-natural-inner)
open ParameterSquareUnits 𝒯 using (unit-square; unit-square-cancel; paste-unitˡ; paste-unitʳ)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

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

```

To compare the two unit routes, paste the composition, identity, and
unit squares, then combine their three whiskered edges. This calculation
uses their specified comparisons and keeps the right-associated route.
The construction `three-comparison-pasting` displays the chosen calculation;
the computation statement identifies the packaged lemma with this pasting.

```agda
three-comparison-pasting : {X Y Z W : CAT}
  {f₀ f₁ f₂ f₃ : MAP X Y} {g₀ g₁ g₂ g₃ : MAP Z W}
  (s : MAP X Z) (t : MAP Y W)
  (α₁ : f₀ =₁ f₁) (α₂ : f₁ =₁ f₂) (α₃ : f₂ =₁ f₃)
  (β₁ : g₀ =₁ g₁) (β₂ : g₁ =₁ g₂) (β₃ : g₂ =₁ g₃)
  (p₀ : (t ∘ f₀) =₁ (g₀ ∘ s)) (p₁ : (t ∘ f₁) =₁ (g₁ ∘ s))
  (p₂ : (t ∘ f₂) =₁ (g₂ ∘ s)) (p₃ : (t ∘ f₃) =₁ (g₃ ∘ s))
  → ((β₁ ▷ s) ∙ p₀) =₂ (p₁ ∙ (t ◁ α₁))
  → ((β₂ ▷ s) ∙ p₁) =₂ (p₂ ∙ (t ◁ α₂))
  → ((β₃ ▷ s) ∙ p₂) =₂ (p₃ ∙ (t ◁ α₃))
  → (p₃ ∙ (t ◁ (α₃ ∙ (α₂ ∙ α₁)))) =₂ (((β₃ ∙ (β₂ ∙ β₁)) ▷ s) ∙ p₀)
three-comparison-pasting s t α₁ α₂ α₃ β₁ β₂ β₃ p₀ p₁ p₂ p₃ first second third =
  let two = paste-squares (t ◁ α₁) (β₁ ▷ s) (t ◁ α₂) (β₂ ▷ s)
        p₀ p₁ p₂ first second
      three = paste-squares ((t ◁ α₂) ∙ (t ◁ α₁)) ((β₂ ▷ s) ∙ (β₁ ▷ s))
        (t ◁ α₃) (β₃ ▷ s) p₀ p₂ p₃ two third
  in isoComp-cong ((pre-three s β₃ β₂ β₁) ⁻¹) (idIso p₀) ∙
    (three ⁻¹ ∙ isoComp-cong (idIso p₃) (post-three t α₃ α₂ α₁))

opaque
  paste-three-comparisons : {X Y Z W : CAT}
    {f₀ f₁ f₂ f₃ : MAP X Y} {g₀ g₁ g₂ g₃ : MAP Z W}
    (s : MAP X Z) (t : MAP Y W)
    (α₁ : f₀ =₁ f₁) (α₂ : f₁ =₁ f₂) (α₃ : f₂ =₁ f₃)
    (β₁ : g₀ =₁ g₁) (β₂ : g₁ =₁ g₂) (β₃ : g₂ =₁ g₃)
    (p₀ : (t ∘ f₀) =₁ (g₀ ∘ s)) (p₁ : (t ∘ f₁) =₁ (g₁ ∘ s))
    (p₂ : (t ∘ f₂) =₁ (g₂ ∘ s)) (p₃ : (t ∘ f₃) =₁ (g₃ ∘ s))
    → ((β₁ ▷ s) ∙ p₀) =₂ (p₁ ∙ (t ◁ α₁))
    → ((β₂ ▷ s) ∙ p₁) =₂ (p₂ ∙ (t ◁ α₂))
    → ((β₃ ▷ s) ∙ p₂) =₂ (p₃ ∙ (t ◁ α₃))
    → (p₃ ∙ (t ◁ (α₃ ∙ (α₂ ∙ α₁)))) =₂ (((β₃ ∙ (β₂ ∙ β₁)) ▷ s) ∙ p₀)
  paste-three-comparisons s t α₁ α₂ α₃ β₁ β₂ β₃ p₀ p₁ p₂ p₃ first second third =
    three-comparison-pasting s t α₁ α₂ α₃ β₁ β₂ β₃ p₀ p₁ p₂ p₃ first second third

  paste-three-comparisons-computation : {X Y Z W : CAT}
    {f₀ f₁ f₂ f₃ : MAP X Y} {g₀ g₁ g₂ g₃ : MAP Z W}
    (s : MAP X Z) (t : MAP Y W)
    (α₁ : f₀ =₁ f₁) (α₂ : f₁ =₁ f₂) (α₃ : f₂ =₁ f₃)
    (β₁ : g₀ =₁ g₁) (β₂ : g₁ =₁ g₂) (β₃ : g₂ =₁ g₃)
    (p₀ : (t ∘ f₀) =₁ (g₀ ∘ s)) (p₁ : (t ∘ f₁) =₁ (g₁ ∘ s))
    (p₂ : (t ∘ f₂) =₁ (g₂ ∘ s)) (p₃ : (t ∘ f₃) =₁ (g₃ ∘ s))
    (first : ((β₁ ▷ s) ∙ p₀) =₂ (p₁ ∙ (t ◁ α₁)))
    (second : ((β₂ ▷ s) ∙ p₁) =₂ (p₂ ∙ (t ◁ α₂)))
    (third : ((β₃ ▷ s) ∙ p₂) =₂ (p₃ ∙ (t ◁ α₃)))
    → (paste-three-comparisons s t α₁ α₂ α₃ β₁ β₂ β₃ p₀ p₁ p₂ p₃ first second third) =₃
      (three-comparison-pasting s t α₁ α₂ α₃ β₁ β₂ β₃ p₀ p₁ p₂ p₃ first second third)
  paste-three-comparisons-computation s t α₁ α₂ α₃ β₁ β₂ β₃ p₀ p₁ p₂ p₃ first second third = idIso _


module Identity {P Q : CAT} (σ : MAP Q P) (C : CAT) where
  private
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
  private
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
          eSquare = paste-natural-outer I.κ I.u κf
            (RQ.retained-identity D) (RP.retained-identity D) I.natural
      in paste-three-comparisons sC sD cQ eQ uQ cP eP uP
        κleft p pUnit κf cSquare eSquare (paste-unitˡ κf)

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
          eSquare = paste-natural-inner κf I.κ I.u
            (RQ.retained-identity C) (RP.retained-identity C) I.natural
      in paste-three-comparisons sC sD cQ eQ uQ cP eP uP
        κright p pUnit κf cSquare eSquare (paste-unitʳ κf)
```


