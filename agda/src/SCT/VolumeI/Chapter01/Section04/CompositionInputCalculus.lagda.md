# Comparing the input boundary with nested application

Using the boundaries from `CompositionInputBaseCalculus`, this module
proves `composition-input-normalization`: following `change-input` by
`target-normalization` agrees with `application-route`.

The proof factors both calculations through their common pairing,
then cancels the comparison routes using the specified projection comparisons.
All chosen comparisons are retained in the resulting identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.CompositionInputBaseCalculus as Base
import SCT.VolumeI.Chapter01.Section04.RetainedParameterChangeProjections as ProjectionCancellation
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.MappingProofCalculus as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.ParameterChangeNaturality as ParameterChangeNaturality
import SCT.VolumeI.Chapter01.Section04.MappingProofCalculus as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section04.EvaluationInputChange as EvaluationInputChange
import SCT.VolumeI.Chapter01.Section04.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section04.EvaluationParameterChange as EvaluationPairs
import SCT.VolumeI.Chapter01.Section04.ParameterChange as ParameterChange

module SCT.VolumeI.Chapter01.Section04.CompositionInputCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open ProjectionCancellation 𝒯 M using (cancel-routes)
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

module Boundaries = Base.Boundaries 𝒯 M

opaque
  cancel-application-corner : {X C D : CAT} {h h′ : MAP X (Map C D)}
    (θ : h =₁ h′) {x y : MAP X C} (β : x =₁ y)
    → (applyTerm-cong (θ ⁻¹) β ∙ applyTerm-cong θ (idIso x)) =₂
        (applyTerm-cong (idIso h) β)
  cancel-application-corner θ β = apply-cong-Iso₂ (isoComp-inverseˡ-at θ) (isoComp-unitʳ-at β) ∙
    (apply-cong-comp (θ ⁻¹) θ β (idIso _)) ⁻¹

  cancel-application-inverse : {X C D : CAT} (h : MAP X (Map C D))
    {x y : MAP X C} (β : x =₁ y)
    → (applyTerm-cong (idIso h) β ∙ applyTerm-cong (idIso h) (β ⁻¹)) =₂
        (idIso (applyTerm h y))
  cancel-application-inverse h {y = y} β = postWhisker-idIso mapEval (pair h y) ∙
    ((postWhisker mapEval ◁ pair-cong-id h y) ∙
    (apply-cong-Iso₂ (isoComp-unitˡ-at (idIso h)) (isoComp-inverseʳ-at β) ∙
      (apply-cong-comp (idIso h) (idIso h) β (β ⁻¹)) ⁻¹))

  cancel-evaluation : {X Y : CAT} {a b c d e : MAP X Y}
    (W : c =₁ d) (v : e =₁ d) (E : b =₁ e) (η : a =₁ b)
    → (W ∙ ((W ⁻¹ ∙ (v ∙ E)) ∙ η)) =₂ (v ∙ (E ∙ η))
  cancel-evaluation W v E η = isoComp-assoc-at v E η ∙
    (isoComp-cong (cancel-inverse W (v ∙ E)) (idIso η) ∙
      (isoComp-assoc-at W (W ⁻¹ ∙ (v ∙ E)) η) ⁻¹)

  final-pasting : {X Y : CAT} {s₀ s₁ s₂ s₃ s₄ t z₀ z₁ z₂ z : MAP X Y}
    (T : t =₁ z) (R : s₄ =₁ t) (A : s₃ =₁ s₄) (G : s₂ =₁ s₃)
    (C : s₁ =₁ s₂) (η : s₀ =₁ s₁)
    (n : s₄ =₁ z₀) (W : z₀ =₁ z₁) (WQ : s₂ =₁ z₂)
    (changed : z₁ =₁ z) (corner : z₂ =₁ z₁)
    (application : z₂ =₁ z) (inverseApplication : z =₁ z₂)
    (application-route : s₀ =₁ z)
    → (T ∙ R) =₂ ((changed ∙ W) ∙ n)
    → (corner ∙ WQ) =₂ (W ∙ (n ∙ (A ∙ G)))
    → (changed ∙ corner) =₂ application
    → (WQ ∙ (C ∙ η)) =₂ (inverseApplication ∙ application-route)
    → (application ∙ inverseApplication) =₂ (idIso z)
    → (T ∙ (R ∙ (A ∙ (G ∙ (C ∙ η))))) =₂ application-route
  final-pasting T R A G C η n W WQ changed corner application inverseApplication application-route
    normal inputChange cancelCorner cancelEvaluation cancelApplication =
    let tail = C ∙ η
        finish = isoComp-unitˡ-at application-route ∙
          (isoComp-cong cancelApplication (idIso application-route) ∙
          ((isoComp-assoc-at application inverseApplication application-route) ⁻¹ ∙
            isoComp-cong (idIso application) cancelEvaluation))
        normalizeTail = isoComp-cong cancelCorner (idIso (WQ ∙ tail)) ∙
          ((isoComp-assoc-at changed corner (WQ ∙ tail)) ⁻¹ ∙
          (isoComp-cong (idIso changed) (isoComp-assoc-at corner WQ tail) ∙
            isoComp-cong (idIso changed) (isoComp-cong (inputChange ⁻¹) (idIso tail))))
        regroupInner = (isoComp-assoc-at W (n ∙ (A ∙ G)) tail) ⁻¹ ∙
          (isoComp-cong (idIso W) ((isoComp-assoc-at n (A ∙ G) tail) ⁻¹) ∙
            isoComp-cong (idIso W) (isoComp-cong (idIso n) ((isoComp-assoc-at A G tail) ⁻¹)))
        regroup = isoComp-cong (idIso changed) regroupInner ∙
          (isoComp-assoc-at changed W (n ∙ (A ∙ (G ∙ tail))) ∙
            isoComp-assoc-at (changed ∙ W) n (A ∙ (G ∙ tail)))
        normalizeStart = isoComp-cong normal (idIso (A ∙ (G ∙ tail))) ∙
          (isoComp-assoc-at T R (A ∙ (G ∙ tail))) ⁻¹
    in finish ∙ (normalizeTail ∙ (regroup ∙ normalizeStart))
module InputNormalization {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P) where

  open Boundaries {C = C} {D = D} {E = E} g f σ
  open Routes {C = C} {D = D} σ using (common; input-route; output-route; input-normalization; output-normalization)
  open Base.InputNormalization 𝒯 M g f σ public
  opaque
    normalize-common-input :
      (common-normalization ∙ (mapUncurry g ◁ input-route f)) =₂
      (changed-evaluation ∙ (mapUncurry g ◁ input-pair))
    normalize-common-input =
      let W = mapUncurry-at g (σ ∘ pr₁) (mapUncurry f ∘ s)
          W′ = mapUncurry-at g (σ ∘ pr₁) (mapUncurry (f ∘ σ))
          pairChange = pair-cong (idIso (σ ∘ pr₁)) inner-change
          input = mapUncurry g ◁ pairChange
          tail = mapUncurry g ◁ input-pair
          action = applyTerm-cong (g ◁ idIso (σ ∘ pr₁)) inner-change
          cancelArgument :
            ((inner-application ∙ inner-change ⁻¹) ∙ inner-change) =₂ inner-application
          cancelArgument = isoComp-unitʳ-at inner-application ∙
            (isoComp-cong (idIso inner-application) (isoComp-inverseˡ-at inner-change) ∙
              isoComp-assoc-at inner-application (inner-change ⁻¹) inner-change)
          cancelFirst : (corner ⁻¹ ∙ (g ◁ idIso (σ ∘ pr₁))) =₂ (corner ⁻¹)
          cancelFirst = isoComp-unitʳ-at (corner ⁻¹) ∙
            isoComp-cong (idIso (corner ⁻¹)) (postWhisker-idIso g (σ ∘ pr₁))
          cancelAction : (common-action ∙ action) =₂ changed-action
          cancelAction = apply-cong-Iso₂ cancelFirst cancelArgument ∙
            (apply-cong-comp (corner ⁻¹) (g ◁ idIso (σ ∘ pr₁))
              (inner-application ∙ inner-change ⁻¹) inner-change) ⁻¹
          natural : (W ∙ input) =₂ (action ∙ W′)
          natural = mapUncurry-at-inner g (idIso (σ ∘ pr₁)) inner-change
      in (isoComp-assoc-at changed-action W′ tail) ⁻¹ ∙
        (isoComp-cong cancelAction (idIso (W′ ∙ tail)) ∙
        ((isoComp-assoc-at common-action action (W′ ∙ tail)) ⁻¹ ∙
        (isoComp-cong (idIso common-action) (isoComp-assoc-at action W′ tail) ∙
        (isoComp-cong (idIso common-action) (isoComp-cong natural (idIso tail)) ∙
        (isoComp-cong (idIso common-action) ((isoComp-assoc-at W input tail) ⁻¹) ∙
        (isoComp-assoc-at common-action W (input ∙ tail) ∙
          isoComp-cong (idIso common-normalization)
            (postWhisker-isoComp-at (mapUncurry g) pairChange input-pair ∙
              (postWhisker (mapUncurry g) ◁ input-factor))))))))

  opaque
    remove-output-route :
      (target-normalization ∙ (mapUncurry g ◁ retained-parameter-change f σ)) =₂
      (common-normalization ∙ (mapUncurry g ◁ input-route f))
    remove-output-route = cancel-routes (mapUncurry g) (output-route f) (input-route f)
      common-normalization (normalization-on-common ⁻¹)
      (idIso (common-normalization ∙ (mapUncurry g ◁ input-route f)))
  opaque
    normalize-input : (target-normalization ∙ change-input) =₂ application-route
    normalize-input =
      let RQ = RetainedEvaluation.retained Q (f ∘ σ)
          WQ = mapUncurry-at (g ∘ σ) pr₁ (mapUncurry (f ∘ σ))
          h = (g ∘ σ) ∘ pr₁
          application = applyTerm-cong (idIso h) inner-application
          inverseApplication = applyTerm-cong (idIso h) (inner-application ⁻¹)
          η = mapUncurryIso (composeTerm-pre g f σ)
      in final-pasting target-normalization
        (mapUncurry g ◁ retained-parameter-change f σ)
        (comp-assoc RQ (productMap σ (id D)) (mapUncurry g))
        (mapUncurry-restrict g σ ▷ RQ)
        (uncurry-compose (g ∘ σ) (f ∘ σ)) η
        (mapUncurry g ◁ input-pair)
        (mapUncurry-at g (σ ∘ pr₁) (mapUncurry (f ∘ σ))) WQ
        changed-action (applyTerm-cong corner (idIso (mapUncurry (f ∘ σ))))
        application inverseApplication application-route
        (normalize-common-input ∙ remove-output-route)
        (mapUncurry-at-input-change g σ pr₁ (mapUncurry (f ∘ σ)))
        (cancel-application-corner corner inner-application)
        (cancel-evaluation WQ inverseApplication (evaluate-compose (g ∘ σ) (f ∘ σ)) η)
        (cancel-application-inverse h inner-application)
composition-input-normalization : {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P)
  →
      (Boundaries.target-normalization g f σ ∙ Boundaries.change-input g f σ) =₂
      (Boundaries.application-route g f σ)
composition-input-normalization = InputNormalization.normalize-input

```
