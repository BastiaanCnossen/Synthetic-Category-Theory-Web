# The input route for composition under parameter change

We normalize the input route through the same application expression used
for the output route. The retained comparison is factored through its
specified common pair, preserving the original choices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.MappingProofCalculus as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.ParameterChangeNaturality as ParameterChangeNaturality
import SCT.VolumeI.Chapter01.Section03.MappingProofCalculus as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section03.EvaluationInputChange as EvaluationInputChange
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.EvaluationParameterChange as EvaluationPairs
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange

module SCT.VolumeI.Chapter01.Section03.CompositionInputBaseCalculus
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


module InputNormalization {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P) where

  open Boundaries {C = C} {D = D} {E = E} g f σ
  open Routes {C = C} {D = D} σ using (common; input-route; output-route; input-normalization; output-normalization)

  s : MAP (Q × C) (P × C)
  s = productMap σ (id C)

  inner-change : =₁ (mapUncurry (f ∘ σ)) (mapUncurry f ∘ s)
  inner-change = mapUncurry-pre f σ

  inner-application : =₁ (mapUncurry (f ∘ σ)) (applyTerm ((f ∘ σ) ∘ pr₁) pr₂)
  inner-application = mapUncurry-as-apply (f ∘ σ)

  corner : =₁ {C = Q × C} ((g ∘ σ) ∘ pr₁) (g ∘ (σ ∘ pr₁))
  corner = comp-assoc pr₁ σ g

  common-action : =₁
    (applyTerm (g ∘ (σ ∘ pr₁)) (mapUncurry f ∘ s)) application-target
  common-action = applyTerm-cong (invIso corner) (inner-application ∙ invIso inner-change)

  common-normalization : =₁ (mapUncurry g ∘ common f) application-target
  common-normalization = common-action ∙ mapUncurry-at g (σ ∘ pr₁) (mapUncurry f ∘ s)

  opaque
    normalization-on-common : =₂ target-normalization
      (common-normalization ∙ (mapUncurry g ◁ output-route f))
    normalization-on-common =
      let β = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
          η = inner-application ∙ invIso inner-change
          Ain = comp-assoc s pr₁ g
          Aret = comp-assoc s (RetainedEvaluation.retained P f) (mapUncurry g)
          a = invIso corner ∙ ((g ◁ β) ∙ Ain)
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
          combineGA : =₂ (G ∙ A)
            (applyTerm-cong ((g ◁ β) ∙ Ain) (idIso (mapUncurry f ∘ s)))
          combineGA = apply-cong-Iso₂ (idIso ((g ◁ β) ∙ Ain)) (isoComp-unitˡ-at _) ∙
            invIso (apply-cong-comp (g ◁ β) Ain (idIso _) (idIso _))
          splitN : =₂ N (common-action ∙ (G ∙ A))
          splitN = invIso
            (apply-cong-Iso₂ (idIso a) (isoComp-unitʳ-at η) ∙
              (invIso (apply-cong-comp (invIso corner) ((g ◁ β) ∙ Ain) η (idIso _)) ∙
                isoComp-cong (idIso common-action) combineGA))
          restriction : =₂ (A ∙ (pre ∙ W)) (W₁ ∙ (pairPre ∙ Aret))
          restriction = mapUncurry-at-restriction g pr₁ (mapUncurry f) s
          natural : =₂ (G ∙ W₁) (W₂ ∙ paired)
          natural = invIso (mapUncurry-at-inner g β (idIso (mapUncurry f ∘ s)))
          lower : =₂ (common-action ∙ (G ∙ (W₁ ∙ (pairPre ∙ Aret))))
            (common-action ∙ (W₂ ∙ (postB ∙ Aret)))
          lower = isoComp-cong (idIso common-action)
            (isoComp-cong (idIso W₂)
              (isoComp-cong (invIso (postWhisker-isoComp-at (mapUncurry g)
                (output-normalization f) (pair-pre pr₁ (mapUncurry f) s))) (idIso Aret)) ∙
              reassociateFour W₂ paired pairPre Aret) ∙
            isoComp-cong (idIso common-action)
              (isoComp-cong natural (idIso (pairPre ∙ Aret)) ∙
                invIso (isoComp-assoc-at G W₁ (pairPre ∙ Aret)))
          beforeCancel : =₂ (N ∙ (pre ∙ W)) ((common-normalization ∙ postB) ∙ Aret)
          beforeCancel = invIso (isoComp-assoc-at common-normalization postB Aret) ∙
            (invIso (isoComp-assoc-at common-action W₂ (postB ∙ Aret)) ∙
            (lower ∙
            (isoComp-cong (idIso common-action) (isoComp-cong (idIso G) restriction) ∙
            (isoComp-cong (idIso common-action) (isoComp-assoc-at G A (pre ∙ W)) ∙
            (isoComp-assoc-at common-action (G ∙ A) (pre ∙ W) ∙
              isoComp-cong splitN (idIso (pre ∙ W)))))))
          regroup : =₂ target-normalization ((N ∙ (pre ∙ W)) ∙ invIso Aret)
          regroup = invIso (isoComp-assoc-at N (pre ∙ W) (invIso Aret)) ∙
            isoComp-cong (idIso N) (invIso (isoComp-assoc-at pre W (invIso Aret)))
      in cancel-right Aret (common-normalization ∙ postB) ∙
        (isoComp-cong beforeCancel (idIso (invIso Aret)) ∙ regroup)



  input-pair : =₁
    (productMap σ (id D) ∘ RetainedEvaluation.retained Q (f ∘ σ))
    (pair (σ ∘ pr₁) (mapUncurry (f ∘ σ)))
  input-pair = AtCoordinates.comparison σ pr₁ (mapUncurry (f ∘ σ))

  opaque
    input-factor : =₂ (input-route f)
      (pair-cong (idIso (σ ∘ pr₁)) inner-change ∙ input-pair)
    input-factor = invIso
      (isoComp-cong
        (pair-cong-Iso₂ (isoComp-unitˡ-at (idIso (σ ∘ pr₁))) (idIso _) ∙
          invIso (pair-cong-comp (idIso (σ ∘ pr₁)) (idIso (σ ∘ pr₁))
            inner-change (comp-unitˡ (mapUncurry (f ∘ σ))))) (idIso _) ∙
        invIso (isoComp-assoc-at (pair-cong (idIso (σ ∘ pr₁)) inner-change)
          (pair-cong (idIso (σ ∘ pr₁)) (comp-unitˡ (mapUncurry (f ∘ σ))))
          (productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ)))))

  changed-action : =₁
    (applyTerm (g ∘ (σ ∘ pr₁)) (mapUncurry (f ∘ σ))) application-target
  changed-action = applyTerm-cong (invIso corner) inner-application

  changed-evaluation : =₁
    (mapUncurry g ∘ pair (σ ∘ pr₁) (mapUncurry (f ∘ σ))) application-target
  changed-evaluation = changed-action ∙ mapUncurry-at g (σ ∘ pr₁) (mapUncurry (f ∘ σ))


``` 
