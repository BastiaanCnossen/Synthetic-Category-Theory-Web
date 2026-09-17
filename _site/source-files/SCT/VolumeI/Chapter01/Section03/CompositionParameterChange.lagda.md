# Composition and change of parameter

The comparison for applying a mapping term commutes with iterated
substitution. We retain the chosen pairing comparisons and the external
associator in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ApplicationRouteNormalization as ApplicationRouteNormalization
import SCT.VolumeI.Chapter01.Section03.NestedApplicationRestriction as NestedApplicationRestriction
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section03.CompositionParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open CompositionNaturality 𝒯 M
  using (coordinate-at)

open Currying 𝒯 M hiding (mapUncurryIso-at)
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


open import SCT.VolumeI.Chapter01.Section03.CompositionRestrictionCalculus 𝒯 M public
open import SCT.VolumeI.Chapter01.Section03.ComparisonCancellation 𝒯 using (cancel-restricted-comparison)

module ComparisonRestriction {R Γ X Y : CAT}
  {F G : MAP X Y} (α : =₁ F G)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : =₁ (q ∘ r) q′)
  {L O : MAP Γ Y} {L′ O′ : MAP R Y}
  (l : =₁ (F ∘ q) L) (l′ : =₁ (F ∘ q′) L′)
  (o : =₁ (G ∘ q) O) (o′ : =₁ (G ∘ q′) O′)
  (u : =₁ (L ∘ r) L′) (v : =₁ (O ∘ r) O′) where

  sourceChange = (F ◁ δ) ∙ comp-assoc r q F
  targetChange = (G ◁ δ) ∙ comp-assoc r q G
  before = o ∙ ((α ▷ q) ∙ invIso l)
  after = o′ ∙ ((α ▷ q′) ∙ invIso l′)

  abstract
    comparison : =₂ (l′ ∙ sourceChange) (u ∙ (l ▷ r))
      → =₂ (o′ ∙ targetChange) (v ∙ (o ▷ r))
      → =₂ (after ∙ u) (v ∙ (before ▷ r))
    comparison leftSquare outputSquare =
      let source = l ▷ r
          beta = (α ▷ q) ▷ r
          beta′ = α ▷ q′
          output = o ▷ r
          sourceSquare = move-square l′ sourceChange u source leftSquare
          betaSquare = comparison-restriction α q r q′ δ
          pasted = paste-squares (beta ∙ invIso source) (beta′ ∙ invIso l′) output o′
            u targetChange v
            (paste-squares (invIso source) (invIso l′) beta beta′ u sourceChange targetChange
              sourceSquare betaSquare) outputSquare
          normalizeRestricted = invIso (preWhisker-isoComp-at o ((α ▷ q) ∙ invIso l) r) ∙
            isoComp-cong (idIso output)
              (invIso (preWhisker-isoComp-at (α ▷ q) (invIso l) r) ∙
                isoComp-cong (idIso beta) (invIso (pre-inverse-at l r)))
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
    left-restriction : =₂ (left′ ∙ sourceChange) (leftOutput ∙ (left ▷ r))
    left-restriction = ApplicationInputRestriction.comparison
      {R = R} {Γ = Γ} {X = Map D E × Map C D} {C = C} {D = E}
      (mapComp {C} {D} {E}) (pair g f) x r (pair (g ∘ r) (f ∘ r)) pairChange
  abstract
    compatibility : =₂
      (apply-compose (g ∘ r) (f ∘ r) (x ∘ r) ∙ leftOutput)
      (rightOutput ∙ (apply-compose g f x ▷ r))
    compatibility = ComparisonRestriction.comparison
      {R = R} {Γ = Γ} {X = (Map D E × Map C D) × C} {Y = E}
      {F = mapUncurry (mapComp {C} {D} {E})} {G = doubleEvaluation {C} {D} {E}}
      (mapComp-β {C} {D} {E}) point r point′ pointChange
      left left′ outer outer′ leftOutput rightOutput left-restriction
      (invIso (isoComp-assoc-at
        (applyTerm-cong (idIso (g ∘ r)) (applyTerm-pre f x r))
        (applyTerm-pre g (applyTerm f x) r) (outer ▷ r)) ∙ outer-restriction)
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
    comparison : =₂ (mapUncurry-as-apply (f ∘ σ))
      (applyTerm-cong mapping-change argument-change ∙
        (applyTerm-pre (f ∘ pr₁) pr₂ substitution ∙
          ((mapUncurry-as-apply f ▷ substitution) ∙ mapUncurry-pre f σ)))
    comparison =
      let A = comp-assoc (pr₁ {Q} {C}) σ f
          first = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc substitution pr₁ f
          α = applyTerm-cong A (idIso pr₂)
          β = applyTerm-cong mapping-change argument-change
          tail = applyTerm-pre (f ∘ pr₁) pr₂ substitution ∙
            ((mapUncurry-as-apply f ▷ substitution) ∙ mapUncurry-pre f σ)
          join = apply-cong-Iso₂ (cancel-forward A first) (isoComp-unitˡ-at argument-change) ∙
            invIso (apply-cong-comp A mapping-change (idIso pr₂) argument-change)
          normalize = isoComp-cong join (idIso tail) ∙ invIso (isoComp-assoc-at α β tail)
      in cancel-left-reflect α
        (invIso normalize ∙ mapUncurry-as-apply-parameter-change f σ)

abstract
  cancel-right-two : {X Y : CAT} {a b c d : MAP X Y}
    (α : =₁ c d) (β : =₁ b c) (γ : =₁ a b)
    → =₂ (((α ∙ (β ∙ γ)) ∙ invIso γ) ∙ invIso β) α
  cancel-right-two α β γ = cancel-right β α ∙
    (isoComp-cong (cancel-right γ (α ∙ β)) (idIso (invIso β)) ∙
      isoComp-cong (isoComp-cong (invIso (isoComp-assoc-at α β γ)) (idIso (invIso γ)))
        (idIso (invIso β)))
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

  restrict-output : =₁ source target
  restrict-output = comp-assoc (productMap σ (id C)) (RetainedEvaluation.retained P f) (mapUncurry g) ∙
    ((uncurry-compose g f ▷ productMap σ (id C)) ∙ mapUncurry-pre (composeTerm g f) σ)

  change-input : =₁ source target
  change-input = (mapUncurry g ◁ retained-parameter-change f σ) ∙
    (comp-assoc (RetainedEvaluation.retained Q (f ∘ σ)) (productMap σ (id D)) (mapUncurry g) ∙
      ((mapUncurry-pre g σ ▷ RetainedEvaluation.retained Q (f ∘ σ)) ∙
        (uncurry-compose (g ∘ σ) (f ∘ σ) ∙ mapUncurryIso (composeTerm-pre g f σ))))

  application-target : MAP (Q × C) E
  application-target = applyTerm ((g ∘ σ) ∘ pr₁) (applyTerm ((f ∘ σ) ∘ pr₁) pr₂)

  application-route : =₁ source application-target
  application-route = evaluate-compose (g ∘ σ) (f ∘ σ) ∙ mapUncurryIso (composeTerm-pre g f σ)

  target-normalization : =₁ target application-target
  target-normalization =
    applyTerm-cong (Coordinates.first C g σ)
      (mapUncurry-as-apply (f ∘ σ) ∙ invIso (mapUncurry-pre f σ)) ∙
    (applyTerm-pre (g ∘ pr₁) (mapUncurry f) (productMap σ (id C)) ∙
      ((mapUncurry-at g pr₁ (mapUncurry f) ▷ productMap σ (id C)) ∙
        invIso (comp-assoc (productMap σ (id C)) (RetainedEvaluation.retained P f) (mapUncurry g))))

  evaluation-route : =₁ source application-target
  evaluation-route = applyTerm-cong (Coordinates.first C g σ)
      (mapUncurry-as-apply (f ∘ σ) ∙ invIso (mapUncurry-pre f σ)) ∙
    (applyTerm-pre (g ∘ pr₁) (mapUncurry f) (productMap σ (id C)) ∙
      (((applyTerm-cong (idIso (g ∘ pr₁)) (invIso (mapUncurry-as-apply f)) ∙
          evaluate-compose g f) ▷ productMap σ (id C)) ∙ mapUncurry-pre (composeTerm g f) σ))

  abstract
    remove-retained-target : =₂ (target-normalization ∙ restrict-output) evaluation-route
    remove-retained-target =
      let s = productMap σ (id C)
          N = applyTerm-cong (Coordinates.first C g σ)
            (mapUncurry-as-apply (f ∘ σ) ∙ invIso (mapUncurry-pre f σ))
          P′ = applyTerm-pre (g ∘ pr₁) (mapUncurry f) s
          W = mapUncurry-at g pr₁ (mapUncurry f)
          U = applyTerm-cong (idIso (g ∘ pr₁)) (invIso (mapUncurry-as-apply f))
          V = evaluate-compose g f
          A = comp-assoc s (RetainedEvaluation.retained P f) (mapUncurry g)
          B = mapUncurry-pre (composeTerm g f) σ
      in cancel-restricted-comparison s W (U ∙ V) A B P′ N

  abstract
    argument-normalization : =₂
      ((mapUncurry-as-apply (f ∘ σ) ∙ invIso (mapUncurry-pre f σ)) ∙
        invIso (mapUncurry-as-apply f ▷ productMap σ (id C)))
      (applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ) ∙
        applyTerm-pre (f ∘ pr₁) pr₂ (productMap σ (id C)))
    argument-normalization =
      let s = productMap σ (id C)
          A = applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ)
          B = applyTerm-pre (f ∘ pr₁) pr₂ s
          C′ = mapUncurry-as-apply f ▷ s
          D′ = mapUncurry-pre f σ
          image = invIso (isoComp-assoc-at A B (C′ ∙ D′)) ∙ AsApplicationChange.comparison f σ
      in cancel-right-two (A ∙ B) C′ D′ ∙
        isoComp-cong (isoComp-cong image (idIso (invIso D′))) (idIso (invIso C′))

  nested-restriction-route : =₁ source application-target
  nested-restriction-route = applyTerm-cong (Coordinates.first C g σ)
      (applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ) ∙
        applyTerm-pre (f ∘ pr₁) pr₂ (productMap σ (id C))) ∙
    (applyTerm-pre (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂) (productMap σ (id C)) ∙
      ((evaluate-compose g f ▷ productMap σ (id C)) ∙ mapUncurry-pre (composeTerm g f) σ))

  module ArgumentTail {S : MAP (P × C) E} {T : MAP (Q × C) E}
    (V : =₁ S (applyTerm (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂)))
    (B : =₁ T (S ∘ productMap σ (id C))) where

    input = applyTerm-cong (Coordinates.first C g σ)
        (mapUncurry-as-apply (f ∘ σ) ∙ invIso (mapUncurry-pre f σ)) ∙
      (applyTerm-pre (g ∘ pr₁) (mapUncurry f) (productMap σ (id C)) ∙
        (((applyTerm-cong (idIso (g ∘ pr₁)) (invIso (mapUncurry-as-apply f)) ∙ V) ▷
          productMap σ (id C)) ∙ B))

    output = applyTerm-cong (Coordinates.first C g σ)
        (applyTerm-cong (Coordinates.first C f σ) (AsApplicationChange.argument-change f σ) ∙
          applyTerm-pre (f ∘ pr₁) pr₂ (productMap σ (id C))) ∙
      (applyTerm-pre (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂) (productMap σ (id C)) ∙
        ((V ▷ productMap σ (id C)) ∙ B))

    abstract
      comparison : =₂ input output
      comparison =
        let s = productMap σ (id C)
            a = Coordinates.first C g σ
            η = mapUncurry-as-apply (f ∘ σ) ∙ invIso (mapUncurry-pre f σ)
            N = applyTerm-cong a η
            before = applyTerm-pre (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂) s
            after = applyTerm-pre (g ∘ pr₁) (mapUncurry f) s
            U = applyTerm-cong (idIso (g ∘ pr₁)) (invIso (mapUncurry-as-apply f))
            U′ = applyTerm-cong (idIso ((g ∘ pr₁) ∘ s)) (invIso (mapUncurry-as-apply f) ▷ s)
            tail = (V ▷ s) ∙ B
            natural = isoComp-cong
                (apply-cong-Iso₂ (preWhisker-idIso (g ∘ pr₁) s) (idIso _)) (idIso before) ∙
              binary-pre-inputs mapEval (idIso (g ∘ pr₁)) (invIso (mapUncurry-as-apply f)) s
            join = apply-cong-Iso₂ (isoComp-unitʳ-at a)
                (argument-normalization ∙ isoComp-cong (idIso η) (pre-inverse-at (mapUncurry-as-apply f) s)) ∙
              invIso (apply-cong-comp a (idIso ((g ∘ pr₁) ∘ s)) η
                (invIso (mapUncurry-as-apply f) ▷ s))
            exchange = isoComp-assoc-at U′ before tail ∙
              (isoComp-cong natural (idIso tail) ∙ invIso (isoComp-assoc-at after (U ▷ s) tail))
            expand = isoComp-cong (idIso after)
              (isoComp-assoc-at (U ▷ s) (V ▷ s) B ∙
                isoComp-cong (preWhisker-isoComp-at U V s) (idIso B))
        in isoComp-cong join (idIso (before ∙ tail)) ∙
          (invIso (isoComp-assoc-at N U′ (before ∙ tail)) ∙
            isoComp-cong (idIso N) (exchange ∙ expand))

  abstract
    normalize-argument : =₂ evaluation-route nested-restriction-route
    normalize-argument = ArgumentTail.comparison
      (evaluate-compose g f) (mapUncurry-pre (composeTerm g f) σ)
  source-coordinate = composeTerm-cong (Coordinates.first C g σ) (Coordinates.first C f σ) ∙
    (composeTerm-pre (g ∘ pr₁) (f ∘ pr₁) (productMap σ (id C)) ∙
      (composeTerm-pre g f pr₁ ▷ productMap σ (id C)))

  common-route : =₁ source application-target
  common-route = apply-compose ((g ∘ σ) ∘ pr₁) ((f ∘ σ) ∘ pr₁) pr₂ ∙
    (applyTerm-cong source-coordinate (AsApplicationChange.argument-change f σ) ∙
      (applyTerm-pre (composeTerm g f ∘ pr₁) pr₂ (productMap σ (id C)) ∙
        ((mapUncurry-as-apply (composeTerm g f) ▷ productMap σ (id C)) ∙
          mapUncurry-pre (composeTerm g f) σ)))

  abstract
    normalize-application-route : =₂ application-route common-route
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
            mapUncurry-pre (composeTerm g f) σ))
        (apply-compose ((g ∘ σ) ∘ pr₁ {Q} {C}) ((f ∘ σ) ∘ pr₁ {Q} {C}) (pr₂ {Q} {C}))
        (BinaryFirstCoordinate.compatibility C (mapComp {C} {D} {E}) g f σ)
        (mapUncurry-as-apply-natural (composeTerm-pre g f σ) ∙
          isoComp-cong (idIso (mapUncurry-as-apply (composeTerm (g ∘ σ) (f ∘ σ))))
            (mapUncurryIso-at (composeTerm-pre g f σ)))
        (AsApplicationChange.comparison (composeTerm g f) σ)
  abstract
    normalize-nested-restriction : =₂ nested-restriction-route common-route
    normalize-nested-restriction =
      NestedApplicationRestriction.Assembly.comparison 𝒯 M
        (g ∘ pr₁ {P} {C}) (f ∘ pr₁ {P} {C}) (pr₂ {P} {C})
        (productMap σ (id C))
        (Coordinates.first C g σ) (Coordinates.first C f σ)
        (AsApplicationChange.argument-change f σ)
        (composeTerm-pre g f (pr₁ {P} {C}))
        (mapUncurry-as-apply (composeTerm g f)) (mapUncurry-pre (composeTerm g f) σ)
        (apply-compose (g ∘ pr₁ {P} {C}) (f ∘ pr₁ {P} {C}) (pr₂ {P} {C}))
        (apply-compose ((g ∘ pr₁ {P} {C}) ∘ productMap σ (id C))
          ((f ∘ pr₁ {P} {C}) ∘ productMap σ (id C)) ((pr₂ {P} {C}) ∘ productMap σ (id C)))
        (apply-compose ((g ∘ σ) ∘ pr₁ {Q} {C}) ((f ∘ σ) ∘ pr₁ {Q} {C}) (pr₂ {Q} {C}))
        (CompositionRestriction.compatibility
          (g ∘ pr₁ {P} {C}) (f ∘ pr₁ {P} {C}) (pr₂ {P} {C}) (productMap σ (id C)))
        (apply-compose-natural (Coordinates.first C g σ) (Coordinates.first C f σ)
          (AsApplicationChange.argument-change f σ))
  abstract
    restrict-output-normalization : =₂ (target-normalization ∙ restrict-output) application-route
    restrict-output-normalization = invIso normalize-application-route ∙
      (normalize-nested-restriction ∙ (normalize-argument ∙ remove-retained-target))
```
