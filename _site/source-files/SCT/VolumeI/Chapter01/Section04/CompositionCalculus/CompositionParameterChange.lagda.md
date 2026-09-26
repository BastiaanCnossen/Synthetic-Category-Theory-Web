# Composition and change of parameter

The comparison for applying a mapping term commutes with iterated
substitution. We retain the chosen pairing comparisons and the external
associator in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRouteNormalization as ApplicationRouteNormalization
import SCT.VolumeI.Chapter01.Section04.Substitution.NestedApplicationRestriction as NestedApplicationRestriction
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open CompositionNaturality 𝒯 M
  using (coordinate-at)

open Currying 𝒯 M hiding (mapUncurry-actions-agree)
open InternalCoherence 𝒯 M using (uncurry-compose; evaluate-compose; module RetainedEvaluation)
open ParameterChange 𝒯 M using (retained-parameter-change)
open ProductSubstitution 𝒯 M using (module Coordinates)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-comp-at)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-id; pair-cong-comp; pair-cong-Iso₂; pair-pre-triangle₁; pair-pre-triangle₂)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
open ProductAssociativity 𝒯 M using (post-pasting; cancel-forward)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; move-square; cancel-left-reflect; cancel-left)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-iterated; pre-inverse-at)


open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionRestrictionCalculus 𝒯 M public
open import SCT.VolumeI.Chapter01.Section04.Substitution.ComparisonCancellation 𝒯 using (cancel-restricted-comparison)

module ComparisonRestriction {R Γ X Y : CAT}
  {F G : MAP X Y} (α : F =₁ G)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : (q ∘ r) =₁ q′)
  {L O : MAP Γ Y} {L′ O′ : MAP R Y}
  (l : (F ∘ q) =₁ L) (l′ : (F ∘ q′) =₁ L′)
  (o : (G ∘ q) =₁ O) (o′ : (G ∘ q′) =₁ O′)
  (u : (L ∘ r) =₁ L′) (v : (O ∘ r) =₁ O′) where

  sourceChange = (F ◁ δ) ∙ comp-assoc r q F
  targetChange = (G ◁ δ) ∙ comp-assoc r q G
  before = o ∙ ((α ▷ q) ∙ l ⁻¹)
  after = o′ ∙ ((α ▷ q′) ∙ l′ ⁻¹)

  abstract
    comparison : (l′ ∙ sourceChange) =₂ (u ∙ (l ▷ r))
      → (o′ ∙ targetChange) =₂ (v ∙ (o ▷ r))
      → (after ∙ u) =₂ (v ∙ (before ▷ r))
    comparison leftSquare outputSquare =
      let source = l ▷ r
          beta = (α ▷ q) ▷ r
          beta′ = α ▷ q′
          output = o ▷ r
          sourceSquare = move-square l′ sourceChange u source leftSquare
          betaSquare = comparison-restriction α q r q′ δ
          pasted = paste-squares (beta ∙ source ⁻¹) (beta′ ∙ l′ ⁻¹) output o′
            u targetChange v
            (paste-squares (source ⁻¹) (l′ ⁻¹) beta beta′ u sourceChange targetChange
              sourceSquare betaSquare) outputSquare
          normalizeRestricted = (preWhisker-isoComp-at o ((α ▷ q) ∙ l ⁻¹) r) ⁻¹ ∙
            isoComp-cong (idIso output)
              ((preWhisker-isoComp-at (α ▷ q) (l ⁻¹) r) ⁻¹ ∙
                isoComp-cong (idIso beta) ((pre-inverse-at l r) ⁻¹))
      in isoComp-cong (idIso v) normalizeRestricted ∙ pasted
module CompositionRestriction {R Γ C D E : CAT}
  (g : MAP Γ (Map D E)) (f : MAP Γ (Map C D)) (x : MAP Γ C) (r : MAP R Γ) where
  open CompositionPoint g f x r

  left = mapUncurry-at (mapComp {C} {D} {E}) (pair g f) x
  left′ = mapUncurry-at (mapComp {C} {D} {E}) (pair (g ∘ r) (f ∘ r)) (x ∘ r)
  sourceChange = (mapUncurry (mapComp {C} {D} {E}) ◁ pointChange) ∙ comp-assoc r point (mapUncurry (mapComp {C} {D} {E}))
  targetChange = ((doubleEvaluation {C} {D} {E}) ◁ pointChange) ∙ comp-assoc r point (doubleEvaluation {C} {D} {E})
  leftOutput = applyTerm-cong (composeTerm-pre g f r) (idIso (x ∘ r)) ∙
    applyTerm-pre (composeTerm g f) x r
  rightOutput = applyTerm-cong (idIso (g ∘ r)) (applyTerm-pre f x r) ∙
    applyTerm-pre g (applyTerm f x) r

  abstract
    left-restriction : (left′ ∙ sourceChange) =₂ (leftOutput ∙ (left ▷ r))
    left-restriction = ApplicationInputRestriction.comparison
      {R = R} {Γ = Γ} {X = Map D E × Map C D} {C = C} {D = E}
      (mapComp {C} {D} {E}) (pair g f) x r (pair (g ∘ r) (f ∘ r)) pairChange
  abstract
    compatibility :
      (apply-compose (g ∘ r) (f ∘ r) (x ∘ r) ∙ leftOutput) =₂
      (rightOutput ∙ (apply-compose g f x ▷ r))
    compatibility = ComparisonRestriction.comparison
      {R = R} {Γ = Γ} {X = (Map D E × Map C D) × C} {Y = E}
      {F = mapUncurry (mapComp {C} {D} {E})} {G = doubleEvaluation {C} {D} {E}}
      (mapComp-β {C} {D} {E}) point r point′ pointChange
      left left′ outer outer′ leftOutput rightOutput left-restriction
      ((isoComp-assoc-at
        (applyTerm-cong (idIso (g ∘ r)) (applyTerm-pre f x r))
        (applyTerm-pre g (applyTerm f x) r) (outer ▷ r)) ⁻¹ ∙ outer-restriction)
apply-compose-restriction = CompositionRestriction.compatibility
```

The application form of an uncurried term can also be expressed using
the first coordinate comparison directly.

```agda
module AsApplicationChange {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P) where
  substitution = productMap σ (id C)
  mapping-change = Coordinates.first C f σ
  argument-change = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)

  abstract
    comparison : (mapUncurry-as-apply (f ∘ σ)) =₂
      (applyTerm-cong mapping-change argument-change ∙
        (applyTerm-pre (f ∘ pr₁) pr₂ substitution ∙
          ((mapUncurry-as-apply f ▷ substitution) ∙ mapUncurry-restrict f σ)))
    comparison =
      let A = comp-assoc (pr₁ {Q} {C}) σ f
          first = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc substitution pr₁ f
          α = applyTerm-cong A (idIso pr₂)
          β = applyTerm-cong mapping-change argument-change
          tail = applyTerm-pre (f ∘ pr₁) pr₂ substitution ∙
            ((mapUncurry-as-apply f ▷ substitution) ∙ mapUncurry-restrict f σ)
          join = apply-cong-Iso₂ (cancel-forward A first) (isoComp-unitˡ-at argument-change) ∙
            (apply-cong-comp A mapping-change (idIso pr₂) argument-change) ⁻¹
          normalize = isoComp-cong join (idIso tail) ∙ (isoComp-assoc-at α β tail) ⁻¹
      in cancel-left-reflect α
        (normalize ⁻¹ ∙ mapUncurry-as-apply-parameter-change f σ)

abstract
  cancel-right-two : {X Y : CAT} {a b c d : MAP X Y}
    (α : c =₁ d) (β : b =₁ c) (γ : a =₁ b)
    → (((α ∙ (β ∙ γ)) ∙ γ ⁻¹) ∙ β ⁻¹) =₂ α
  cancel-right-two α β γ = cancel-right β α ∙
    (isoComp-cong (cancel-right γ (α ∙ β)) (idIso (β ⁻¹)) ∙
      isoComp-cong (isoComp-cong ((isoComp-assoc-at α β γ) ⁻¹) (idIso (γ ⁻¹)))
        (idIso (β ⁻¹)))
```

The uncurried composition square has the following two boundaries. Both
start with the restricted composite and end with evaluation while retaining
the original parameter.

```agda
module UncurriedCompositionRestriction {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P) where

  source : MAP (Q × C) E
  source = mapUncurry (composeTerm g f ∘ σ)

  target : MAP (Q × C) E
  target = mapUncurry g ∘ (RetainedEvaluation.retained P f ∘ productMap σ (id C))

  restrict-output : source =₁ target
  restrict-output = comp-assoc (productMap σ (id C)) (RetainedEvaluation.retained P f) (mapUncurry g) ∙
    ((uncurry-compose g f ▷ productMap σ (id C)) ∙ mapUncurry-restrict (composeTerm g f) σ)

  change-input : source =₁ target
  change-input = (mapUncurry g ◁ retained-parameter-change f σ) ∙
    (comp-assoc (RetainedEvaluation.retained Q (f ∘ σ)) (productMap σ (id D)) (mapUncurry g) ∙
      ((mapUncurry-restrict g σ ▷ RetainedEvaluation.retained Q (f ∘ σ)) ∙
        (uncurry-compose (g ∘ σ) (f ∘ σ) ∙ mapUncurryIso (composeTerm-pre g f σ))))

  application-target : MAP (Q × C) E
  application-target = applyTerm ((g ∘ σ) ∘ pr₁) (applyTerm ((f ∘ σ) ∘ pr₁) pr₂)

  application-route : source =₁ application-target
  application-route = evaluate-compose (g ∘ σ) (f ∘ σ) ∙ mapUncurryIso (composeTerm-pre g f σ)

  target-normalization : target =₁ application-target
  target-normalization =
    applyTerm-cong (Coordinates.first C g σ)
      (mapUncurry-as-apply (f ∘ σ) ∙ (mapUncurry-restrict f σ) ⁻¹) ∙
    (applyTerm-pre (g ∘ pr₁) (mapUncurry f) (productMap σ (id C)) ∙
      ((mapUncurry-at g pr₁ (mapUncurry f) ▷ productMap σ (id C)) ∙
        (comp-assoc (productMap σ (id C)) (RetainedEvaluation.retained P f) (mapUncurry g)) ⁻¹))

  evaluation-route : source =₁ application-target
  evaluation-route = applyTerm-cong (Coordinates.first C g σ)
      (mapUncurry-as-apply (f ∘ σ) ∙ (mapUncurry-restrict f σ) ⁻¹) ∙
    (applyTerm-pre (g ∘ pr₁) (mapUncurry f) (productMap σ (id C)) ∙
      (((applyTerm-cong (idIso (g ∘ pr₁)) ((mapUncurry-as-apply f) ⁻¹) ∙
          evaluate-compose g f) ▷ productMap σ (id C)) ∙ mapUncurry-restrict (composeTerm g f) σ))

  abstract
    remove-retained-target : (target-normalization ∙ restrict-output) =₂ evaluation-route
    remove-retained-target =
      let s = productMap σ (id C)
          N = applyTerm-cong (Coordinates.first C g σ)
            (mapUncurry-as-apply (f ∘ σ) ∙ (mapUncurry-restrict f σ) ⁻¹)
          P′ = applyTerm-pre (g ∘ pr₁) (mapUncurry f) s
          W = mapUncurry-at g pr₁ (mapUncurry f)
          U = applyTerm-cong (idIso (g ∘ pr₁)) ((mapUncurry-as-apply f) ⁻¹)
          V = evaluate-compose g f
          A = comp-assoc s (RetainedEvaluation.retained P f) (mapUncurry g)
          B = mapUncurry-restrict (composeTerm g f) σ
      in cancel-restricted-comparison s W (U ∙ V) A B P′ N

  abstract
    argument-normalization :
      ((mapUncurry-as-apply (f ∘ σ) ∙ (mapUncurry-restrict f σ) ⁻¹) ∙
        (mapUncurry-as-apply f ▷ productMap σ (id C)) ⁻¹) =₂
      (applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ) ∙
        applyTerm-pre (f ∘ pr₁) pr₂ (productMap σ (id C)))
    argument-normalization =
      let s = productMap σ (id C)
          A = applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ)
          B = applyTerm-pre (f ∘ pr₁) pr₂ s
          C′ = mapUncurry-as-apply f ▷ s
          D′ = mapUncurry-restrict f σ
          image = (isoComp-assoc-at A B (C′ ∙ D′)) ⁻¹ ∙ AsApplicationChange.comparison f σ
      in cancel-right-two (A ∙ B) C′ D′ ∙
        isoComp-cong (isoComp-cong image (idIso (D′ ⁻¹))) (idIso (C′ ⁻¹))

  nested-restriction-route : source =₁ application-target
  nested-restriction-route = applyTerm-cong (Coordinates.first C g σ)
      (applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ) ∙
        applyTerm-pre (f ∘ pr₁) pr₂ (productMap σ (id C))) ∙
    (applyTerm-pre (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂) (productMap σ (id C)) ∙
      ((evaluate-compose g f ▷ productMap σ (id C)) ∙ mapUncurry-restrict (composeTerm g f) σ))

  module ArgumentTail {S : MAP (P × C) E} {T : MAP (Q × C) E}
    (V : S =₁ (applyTerm (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂)))
    (B : T =₁ (S ∘ productMap σ (id C))) where

    input = applyTerm-cong (Coordinates.first C g σ)
        (mapUncurry-as-apply (f ∘ σ) ∙ (mapUncurry-restrict f σ) ⁻¹) ∙
      (applyTerm-pre (g ∘ pr₁) (mapUncurry f) (productMap σ (id C)) ∙
        (((applyTerm-cong (idIso (g ∘ pr₁)) ((mapUncurry-as-apply f) ⁻¹) ∙ V) ▷
          productMap σ (id C)) ∙ B))

    output = applyTerm-cong (Coordinates.first C g σ)
        (applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ) ∙
          applyTerm-pre (f ∘ pr₁) pr₂ (productMap σ (id C))) ∙
      (applyTerm-pre (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂) (productMap σ (id C)) ∙
        ((V ▷ productMap σ (id C)) ∙ B))

    abstract
      comparison : input =₂ output
      comparison =
        let s = productMap σ (id C)
            a = Coordinates.first C g σ
            η = mapUncurry-as-apply (f ∘ σ) ∙ (mapUncurry-restrict f σ) ⁻¹
            N = applyTerm-cong a η
            before = applyTerm-pre (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂) s
            after = applyTerm-pre (g ∘ pr₁) (mapUncurry f) s
            U = applyTerm-cong (idIso (g ∘ pr₁)) ((mapUncurry-as-apply f) ⁻¹)
            U′ = applyTerm-cong (idIso ((g ∘ pr₁) ∘ s)) ((mapUncurry-as-apply f) ⁻¹ ▷ s)
            tail = (V ▷ s) ∙ B
            natural = isoComp-cong
                (apply-cong-Iso₂ (preWhisker-idIso (g ∘ pr₁) s) (idIso _)) (idIso before) ∙
              binary-pre-inputs mapEval (idIso (g ∘ pr₁)) ((mapUncurry-as-apply f) ⁻¹) s
            join = apply-cong-Iso₂ (isoComp-unitʳ-at a)
                (argument-normalization ∙ isoComp-cong (idIso η) (pre-inverse-at (mapUncurry-as-apply f) s)) ∙
              (apply-cong-comp a (idIso ((g ∘ pr₁) ∘ s)) η
                ((mapUncurry-as-apply f) ⁻¹ ▷ s)) ⁻¹
            exchange = isoComp-assoc-at U′ before tail ∙
              (isoComp-cong natural (idIso tail) ∙ (isoComp-assoc-at after (U ▷ s) tail) ⁻¹)
            expand = isoComp-cong (idIso after)
              (isoComp-assoc-at (U ▷ s) (V ▷ s) B ∙
                isoComp-cong (preWhisker-isoComp-at U V s) (idIso B))
        in isoComp-cong join (idIso (before ∙ tail)) ∙
          ((isoComp-assoc-at N U′ (before ∙ tail)) ⁻¹ ∙
            isoComp-cong (idIso N) (exchange ∙ expand))

  abstract
    normalize-argument : evaluation-route =₂ nested-restriction-route
    normalize-argument = ArgumentTail.comparison
      (evaluate-compose g f) (mapUncurry-restrict (composeTerm g f) σ)
  source-coordinate = composeTerm-cong (Coordinates.first C g σ) (Coordinates.first C f σ) ∙
    (composeTerm-pre (g ∘ pr₁) (f ∘ pr₁) (productMap σ (id C)) ∙
      (composeTerm-pre g f pr₁ ▷ productMap σ (id C)))

  common-route : source =₁ application-target
  common-route = apply-compose ((g ∘ σ) ∘ pr₁) ((f ∘ σ) ∘ pr₁) pr₂ ∙
    (applyTerm-cong source-coordinate (AsApplicationChange.argument-change f σ) ∙
      (applyTerm-pre (composeTerm g f ∘ pr₁) pr₂ (productMap σ (id C)) ∙
        ((mapUncurry-as-apply (composeTerm g f) ▷ productMap σ (id C)) ∙
          mapUncurry-restrict (composeTerm g f) σ)))

  abstract
    normalize-application-route : application-route =₂ common-route
    normalize-application-route =
      ApplicationRouteNormalization.Assembly.comparison 𝒯 M
        (composeTerm-pre (g ∘ σ) (f ∘ σ) (pr₁ {Q} {C}))
        (composeTerm-pre g f σ ▷ pr₁ {Q} {C})
        (Coordinates.first C (composeTerm g f) σ)
        (AsApplicationChange.argument-change f σ) source-coordinate
        (mapUncurry-as-apply (composeTerm (g ∘ σ) (f ∘ σ)))
        (mapUncurryIso (composeTerm-pre g f σ))
        (mapUncurry-as-apply (composeTerm g f ∘ σ))
        (applyTerm-pre (composeTerm g f ∘ pr₁ {P} {C}) (pr₂ {P} {C}) (productMap σ (id C)) ∙
          ((mapUncurry-as-apply (composeTerm g f) ▷ productMap σ (id C)) ∙
            mapUncurry-restrict (composeTerm g f) σ))
        (apply-compose ((g ∘ σ) ∘ pr₁ {Q} {C}) ((f ∘ σ) ∘ pr₁ {Q} {C}) (pr₂ {Q} {C}))
        (BinaryFirstCoordinate.compatibility C (mapComp {C} {D} {E}) g f σ)
        (mapUncurry-as-apply-natural (composeTerm-pre g f σ) ∙
          isoComp-cong (idIso (mapUncurry-as-apply (composeTerm (g ∘ σ) (f ∘ σ))))
            (mapUncurry-actions-agree (composeTerm-pre g f σ)))
        (AsApplicationChange.comparison (composeTerm g f) σ)
  abstract
    normalize-nested-restriction : nested-restriction-route =₂ common-route
    normalize-nested-restriction =
      NestedApplicationRestriction.Assembly.comparison 𝒯 M
        (g ∘ pr₁ {P} {C}) (f ∘ pr₁ {P} {C}) (pr₂ {P} {C})
        (productMap σ (id C))
        (Coordinates.first C g σ) (Coordinates.first C f σ)
        (AsApplicationChange.argument-change f σ)
        (composeTerm-pre g f (pr₁ {P} {C}))
        (mapUncurry-as-apply (composeTerm g f)) (mapUncurry-restrict (composeTerm g f) σ)
        (apply-compose (g ∘ pr₁ {P} {C}) (f ∘ pr₁ {P} {C}) (pr₂ {P} {C}))
        (apply-compose ((g ∘ pr₁ {P} {C}) ∘ productMap σ (id C))
          ((f ∘ pr₁ {P} {C}) ∘ productMap σ (id C)) ((pr₂ {P} {C}) ∘ productMap σ (id C)))
        (apply-compose ((g ∘ σ) ∘ pr₁ {Q} {C}) ((f ∘ σ) ∘ pr₁ {Q} {C}) (pr₂ {Q} {C}))
        (CompositionRestriction.compatibility
          (g ∘ pr₁ {P} {C}) (f ∘ pr₁ {P} {C}) (pr₂ {P} {C}) (productMap σ (id C)))
        (apply-compose-natural (Coordinates.first C g σ) (Coordinates.first C f σ)
          (AsApplicationChange.argument-change f σ))
  abstract
    restrict-output-normalization : (target-normalization ∙ restrict-output) =₂ application-route
    restrict-output-normalization = normalize-application-route ⁻¹ ∙
      (normalize-nested-restriction ∙ (normalize-argument ∙ remove-retained-target))
```
