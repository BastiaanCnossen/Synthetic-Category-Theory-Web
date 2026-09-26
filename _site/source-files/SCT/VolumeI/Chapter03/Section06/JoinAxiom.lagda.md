# The two join axioms

This interface records `axiom:K_Joins` and
`axiom:K2_Join_As_Dependent_Product`. A single chosen join and height
serve both axioms. The pushout clause is required over anima bases;
the dependent-product clause quantifies over arbitrary absolute bases.
This is not an assertion of arbitrary contextual validity.

The boundary comparison is constructed from the supplied height
identification. Its actual inverse, with its induced triangle, is the
evaluation in the dependent-product clause.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level) renaming (_⊔_ to _⊔ℓ_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section06.JoinAxiom
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P using (IsDependentProduct)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I

record JoinData : Set (c ⊔ℓ m) where
  field
    JoinOver : {C D Γ : CAT} → MAP C Γ → MAP D Γ → CAT
    height : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) → MAP (JoinOver p q) (Γ × [1])
    inclusion : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) → MAP (C ⊔ D) (JoinOver p q)
    height-boundary : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) →
      (height p q ∘ inclusion p q) =₁ Span.boundary-height p q

  projection : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) → MAP (JoinOver p q) Γ
  projection p q = pr₁ ∘ height p q

record JoinPushout (J : JoinData) {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) : Set (c ⊔ℓ m) where
  open JoinData J
  module Diagram = Span p q
  field
    cylinder : MAP (Diagram.W × [1]) (JoinOver p q)
    matching : (cylinder ∘ Diagram.top) =₁ (inclusion p q ∘ Diagram.left)

  square : Square Diagram.top Diagram.left cylinder (inclusion p q)
  square = record { commute = matching }
  cocone : Cocone Diagram.top Diagram.left (JoinOver p q)
  cocone = record { left = cylinder ; right = inclusion p q ; match = matching }

  field
    universal : IsPushout square
    height-cylinder : (height p q ∘ cylinder) =₁ Diagram.cylinder-height
    height-compatible :
      (Diagram.height-match ∙ (height-cylinder ▷ Diagram.top)) =₂
      ((height-boundary p q ▷ Diagram.left) ∙ Cocone.match (coconePost (height p q) cocone))

  height-comparison : CoconeIso (coconePost (height p q) cocone) Diagram.height-cocone
  height-comparison = record
    { leftIso = height-cylinder ; rightIso = height-boundary p q ; compatible = height-compatible }

module BoundaryComparison (J : JoinData) {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) where
  open JoinData J
  module Endpoint = Boundary p q

  cone : Cone (height p q) (weakened-boundary Γ) (C ⊔ D)
  cone = record
    { left = inclusion p q ; right = Endpoint.projection
    ; match = (Endpoint.comparison) ⁻¹ ∙ height-boundary p q }

  functor : MAP (C ⊔ D) (Pullback (height p q) (weakened-boundary Γ))
  functor = pullbackLift cone

  abstract
    comparison : ConeIso (conePre functor (pullbackCone (height p q) (weakened-boundary Γ))) cone
    comparison = pullbackLift-β cone

    evaluation : IsEquiv functor → FunctorOver (pullback₂ {f = height p q} {weakened-boundary Γ}) Endpoint.projection
    evaluation e = record
      { lift = IsEquiv.inverse e
      ; comparison = comp-unitʳ pullback₂ ∙
        ((pullback₂ ◁ (IsEquiv.retractionIso e) ⁻¹) ∙
          (comp-assoc (IsEquiv.inverse e) functor pullback₂ ∙
            ((ConeIso.rightIso comparison ▷ IsEquiv.inverse e) ⁻¹))) }

    evaluation-underlying : (e : IsEquiv functor) →
      FunctorLift.lift (evaluation e) =₁ IsEquiv.inverse e
    evaluation-underlying e = idIso _

record JoinAxiom : Set (c ⊔ℓ m ⊔ℓ a) where
  field
    dataJoin : JoinData
  open JoinData dataJoin public
  field
    mapping-out : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) → isAn Γ → JoinPushout dataJoin p q
    boundary-isEquiv : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) → IsEquiv (BoundaryComparison.functor dataJoin p q)
    mapping-in : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) →
      IsDependentProduct (weakened-boundary Γ) (Boundary.projection p q) (height p q)
        (BoundaryComparison.evaluation dataJoin p q (boundary-isEquiv p q))
```
