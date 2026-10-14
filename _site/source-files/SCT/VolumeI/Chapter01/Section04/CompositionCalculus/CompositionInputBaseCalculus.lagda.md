# Boundaries for composition under parameter change

There are two comparisons from the uncurried restricted composite to
successive evaluation with the original parameter retained. `restrict-output`
uses the restriction comparison for the composite; `change-input` uses
the restriction comparison for its inner factor.

`Boundaries` names their common source and target and the nested application
expression used to compare them. `InputNormalization` prepares the
factorization of `change-input` through that expression. The proof is
completed in `CompositionInputCalculus`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.Calculus.Squares as Squares
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.Substitution.MappingProofCalculus as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChangeNaturality as ParameterChangeNaturality
import SCT.VolumeI.Chapter01.Section04.Substitution.MappingProofCalculus as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationInputChange as EvaluationInputChange
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationParameterChange as EvaluationPairs
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange as ParameterChange

module SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionInputBaseCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open CompositionNaturality 𝒯 M using (apply-cong-comp; apply-cong-Iso₂; mapUncurry-at-inner)
open InternalCoherence 𝒯 M using (uncurry-compose; evaluate-compose; module RetainedEvaluation)
open EvaluationParameterChange 𝒯 M using (mapUncurry-at-restriction)
open EvaluationInputChange 𝒯 M using (mapUncurry-at-input-change)
module AtCoordinates = EvaluationPairs.AtCoordinates 𝒯 M
open ParameterChange 𝒯 M using (retained-parameter-change)
module Routes = ParameterChangeNaturality.Routes 𝒯 M
open ProductSubstitution 𝒯 M using (module Coordinates)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour; cancel-inverse)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; cancel-left-reflect)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂; pair-cong-id)

module Boundaries {P Q C D E : CAT}
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


module InputNormalization {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P) where

  open Boundaries {C = C} {D = D} {E = E} g f σ
  open Routes {C = C} {D = D} σ using (common; input-route; output-route; input-normalization; output-normalization)

  s : MAP (Q × C) (P × C)
  s = productMap σ (id C)

  inner-change : (mapUncurry (f ∘ σ)) =₁ (mapUncurry f ∘ s)
  inner-change = mapUncurry-restrict f σ

  inner-application : (mapUncurry (f ∘ σ)) =₁ (applyTerm ((f ∘ σ) ∘ pr₁) pr₂)
  inner-application = mapUncurry-as-apply (f ∘ σ)

  corner : _=₁_ {C = Q × C} ((g ∘ σ) ∘ pr₁) (g ∘ (σ ∘ pr₁))
  corner = comp-assoc pr₁ σ g

  common-action :
    (applyTerm (g ∘ (σ ∘ pr₁)) (mapUncurry f ∘ s)) =₁ application-target
  common-action = applyTerm-cong (corner ⁻¹) (inner-application ∙ inner-change ⁻¹)

  common-normalization : (mapUncurry g ∘ common f) =₁ application-target
  common-normalization = common-action ∙ mapUncurry-at g (σ ∘ pr₁) (mapUncurry f ∘ s)

  opaque
    normalization-on-common : target-normalization =₂
      (common-normalization ∙ (mapUncurry g ◁ output-route f))
    normalization-on-common =
      let β = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
          η = inner-application ∙ inner-change ⁻¹
          Ain = comp-assoc s pr₁ g
          Aret = comp-assoc s (RetainedEvaluation.retained P f) (mapUncurry g)
          a = corner ⁻¹ ∙ ((g ◁ β) ∙ Ain)
          N = applyTerm-cong a η
          G = applyTerm-cong (g ◁ β) (idIso (mapUncurry f ∘ s))
          A = applyTerm-cong Ain (idIso (mapUncurry f ∘ s))
          pre = applyTerm-pre (g ∘ pr₁) (mapUncurry f) s
          W = mapUncurry-at g pr₁ (mapUncurry f) ▷ s
          W₁ = mapUncurry-at g (pr₁ ∘ s) (mapUncurry f ∘ s)
          W₂ = mapUncurry-at g (σ ∘ pr₁) (mapUncurry f ∘ s)
          paired = mapUncurry g ◁ output-normalization f
          pairPre = mapUncurry g ◁ pair-pre pr₁ (mapUncurry f) s
          postB = mapUncurry g ◁ output-route f
          combineGA : (G ∙ A) =₂
            (applyTerm-cong ((g ◁ β) ∙ Ain) (idIso (mapUncurry f ∘ s)))
          combineGA = apply-cong-Iso₂ (idIso ((g ◁ β) ∙ Ain)) (isoComp-unitˡ-at _) ∙
            (apply-cong-comp (g ◁ β) Ain (idIso _) (idIso _)) ⁻¹
          splitN : N =₂ (common-action ∙ (G ∙ A))
          splitN =
            (apply-cong-Iso₂ (idIso a) (isoComp-unitʳ-at η) ∙
              ((apply-cong-comp (corner ⁻¹) ((g ◁ β) ∙ Ain) η (idIso _)) ⁻¹ ∙
                isoComp-cong (idIso common-action) combineGA)) ⁻¹
          restriction : (A ∙ (pre ∙ W)) =₂ (W₁ ∙ (pairPre ∙ Aret))
          restriction = mapUncurry-at-restriction g pr₁ (mapUncurry f) s
          natural : (G ∙ W₁) =₂ (W₂ ∙ paired)
          natural = (mapUncurry-at-inner g β (idIso (mapUncurry f ∘ s))) ⁻¹
      in Squares.common-frame-pasting
        (comparisonAlgebra (Q × C) E) (comparisonLaws (Q × C) E)
        common-action G A N pre W W₁ W₂ paired pairPre postB Aret (Aret ⁻¹)
        splitN restriction natural
        ((postWhisker-isoComp-at (mapUncurry g)
          (output-normalization f) (pair-pre pr₁ (mapUncurry f) s)) ⁻¹)
        (reassociateFour W₂ paired pairPre Aret)
        (cancel-right Aret (common-normalization ∙ postB))


  input-pair :
    (productMap σ (id D) ∘ RetainedEvaluation.retained Q (f ∘ σ)) =₁
    (pair (σ ∘ pr₁) (mapUncurry (f ∘ σ)))
  input-pair = AtCoordinates.comparison σ pr₁ (mapUncurry (f ∘ σ))

  opaque
    input-factor : (input-route f) =₂
      (pair-cong (idIso (σ ∘ pr₁)) inner-change ∙ input-pair)
    input-factor =
      (isoComp-cong
        (pair-cong-Iso₂ (isoComp-unitˡ-at (idIso (σ ∘ pr₁))) (idIso _) ∙
          (pair-cong-comp (idIso (σ ∘ pr₁)) (idIso (σ ∘ pr₁))
            inner-change (comp-unitˡ (mapUncurry (f ∘ σ)))) ⁻¹) (idIso _) ∙
        (isoComp-assoc-at (pair-cong (idIso (σ ∘ pr₁)) inner-change)
          (pair-cong (idIso (σ ∘ pr₁)) (comp-unitˡ (mapUncurry (f ∘ σ))))
          (productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ)))) ⁻¹) ⁻¹

  changed-action :
    (applyTerm (g ∘ (σ ∘ pr₁)) (mapUncurry (f ∘ σ))) =₁ application-target
  changed-action = applyTerm-cong (corner ⁻¹) inner-application

  changed-evaluation :
    (mapUncurry g ∘ pair (σ ∘ pr₁) (mapUncurry (f ∘ σ))) =₁ application-target
  changed-evaluation = changed-action ∙ mapUncurry-at g (σ ∘ pr₁) (mapUncurry (f ∘ σ))


``` 
