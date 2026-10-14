# Complete comparisons of relative families

Evaluation of the named structural functor is natural in its terminal
coordinate. This square carries complete fiber identifications to complete
comparisons of families over the base. In particular, the chosen family
factor recovers the supplied base triangle as well as its underlying functor.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativeFamilyComparisons where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; preWhisker-id₌; comp-unitˡ; comp-assoc;
    module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation
  using (evaluate-restrict-substitution)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Functoriality
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName-β)
open import SCT.VolumeI.Chapter01.Section09.NamedEvaluation
open import SCT.VolumeI.Chapter01.Section09.RelativeFunctorCategories

private
  module _ {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {u : x″ ＝ y″}
      {l : x =₁ x′} {r : y =₁ y′} {l′ : x′ =₁ x″} {r′ : y′ =₁ y″}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b u (const l′) (const r′)
      → SquareCell₌ t u (const (l′ ∙ l)) (const (r′ ∙ r))
    paste-fixed {l = l} {r} {l′} {r′} a b =
      replace-sides₌ (const-comp l′ l) (const-comp r′ r) (paste-square₌ a b)

    constant-endpoints : {A B : CAT Γ} {x x′ y y′ : MAP A B}
      (p : x =₁ x′) (q : y =₁ y′) (α : x =₁ y)
      → changeEndpoints (const {P = X} p) (const q) (const α) =₁ const (changeEndpoints p q α)
    constant-endpoints p q α = const-comp q (α ∙ p ⁻¹) ∙
      comp₌-cong (id₌ (const q))
        (const-comp α (p ⁻¹) ∙ comp₌-cong (id₌ (const α)) ((const-inv p) ⁻¹))

    evaluation-square : {F C D T : CAT Γ} (e : MAP (F × C) D)
      {f g f′ g′ : MAP T F} {α : f ＝ g} {β : f′ ＝ g′} {p : f ＝ f′} {q : g ＝ g′}
      → SquareCell₌ α β p q
      → SquareCell₌ (evaluate⁼ e α) (evaluate⁼ e β) (evaluate⁼ e p) (evaluate⁼ e q)
    evaluation-square e {α = α} {β} {p} {q} square = evaluate⁼-composition e β p ∙
      (evaluate⁼-cong e square ∙ (evaluate⁼-composition e q α) ⁻¹)

module RelativeFamilies {Γ : Context} {S : CAT Γ} (A B : CategoryOverBase S) where
  module L = RelativeFunctorCategory A B
  private
    C D : CAT Γ
    C = CategoryOverBase.category A
    D = CategoryOverBase.category B
    p : MAP C S
    p = CategoryOverBase.map A
    q : MAP D S
    q = CategoryOverBase.map B
    eD : MAP (Fun C D × C) D
    eD = funEval {C = C} {D = D}
    eS : MAP (Fun C S × C) S
    eS = funEval {C = C} {D = S}

  open NamedEvaluation {C = C} {S = S} p public using (named-evaluation-inputs)

  family-cone : {K : CAT Γ} → L.Family K → Cone q p (K × C)
  family-cone F = record
    { left = FunctorOverBase.functor F; right = pr₂; match = FunctorOverBase.cell F }

  evaluated-cone : {K : CAT Γ} → Cone L.postcomposition L.point K → Cone q p (K × C)
  evaluated-cone s = record
    { left = evaluate eD (Cone.left s); right = pr₂
    ; match = changeEndpoints
        (funPost-uncurry {C = C} {D = D} {E = S} q (Cone.left s))
        (L.named-evaluation (Cone.right s)) (evaluate-cong eS (Cone.match s)) }

  module _ {X K : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    private
      matching-normal : (z : Cone L.postcomposition L.point K) →
        changeEndpoints
          (const {P = X} (funPost-uncurry {C = C} {D = D} {E = S} q (Cone.left z)))
          (const {P = X} (L.named-evaluation (Cone.right z))) (evaluate⁼ eS (const {P = X} (Cone.match z))) =₁
          const {P = X} (Cone.match (evaluated-cone z))
      matching-normal z = constant-endpoints {X = X}
        (funPost-uncurry {C = C} {D = D} {E = S} q (Cone.left z))
        (L.named-evaluation (Cone.right z)) (evaluate-cong eS (Cone.match z)) ∙
        changeEndpoints-cong
          (const {P = X} (funPost-uncurry {C = C} {D = D} {E = S} q (Cone.left z)))
          (const {P = X} (L.named-evaluation (Cone.right z))) (evaluate⁼-constant eS (Cone.match z))

    evaluated-identification : {s t : Cone L.postcomposition L.point K}
      → ConeIdentification X s t → ConeIdentification X (evaluated-cone s) (evaluated-cone t)
    evaluated-identification {s} {t} Φ = record
      { left = evaluate⁼ eD (ConeIdentification.left Φ)
      ; right = const (id₌ pr₂)
      ; compatible = replace-edges₌ (id₌ _)
          ((const-cong (postWhisker-id₌ p pr₂) ∙ post-constant p (id₌ pr₂)) ⁻¹)
          (replace-sides₌ (matching-normal s) (matching-normal t) (transport-square
            (const (funPost-uncurry {C = C} {D = D} {E = S} q (Cone.left s)))
            (const (funPost-uncurry {C = C} {D = D} {E = S} q (Cone.left t)))
            (const (L.named-evaluation (Cone.right s))) (const (L.named-evaluation (Cone.right t)))
            (evaluate⁼ eS (const (Cone.match s))) (evaluate⁼ eS (const (Cone.match t)))
            (evaluate⁼ eS (L.postcomposition ◁ ConeIdentification.left Φ))
            (evaluate⁼ eS (L.point ◁ ConeIdentification.right Φ))
            (q ◁ evaluate⁼ eD (ConeIdentification.left Φ)) (const (id₌ (p ∘ pr₂)))
            (funPost-uncurry-inputs {C = C} {D = D} {E = S} q (ConeIdentification.left Φ))
            (named-evaluation-inputs (ConeIdentification.right Φ))
            (evaluation-square eS (ConeIdentification.compatible Φ)))) }

  evaluated-identification-One : {K : CAT Γ} {s t : Cone L.postcomposition L.point K}
    → ConeIdentification₁ s t → ConeIdentification₁ (evaluated-cone s) (evaluated-cone t)
  evaluated-identification-One Φ = record
    { left = evaluate-cong eD (ConeIdentification₁.left Φ); right = id₌ pr₂
    ; compatible = replace-edges₌
        (postWhisker q ◁ evaluate⁼-absolute eD (ConeIdentification₁.left Φ))
        (postWhisker p ◁ const-One (id₌ pr₂))
        (ConeIdentification₁.compatible
          (cone-identification-One (evaluated-identification (cone-identification Φ)))) }

  module FamilyComputation {K : CAT Γ} (F : L.Family K) where
    private
      module Chosen = L.ChosenFamily F
      desired : (q ∘ evaluate eD Chosen.curried) =₁ (p ∘ pr₂ {C = K} {D = C})
      desired = FunctorOverBase.cell F ∙ (q ◁ Chosen.curry-computation)

    encoded-comparison : ConeIdentification₁ (evaluated-cone Chosen.encoded) (family-cone F)
    encoded-comparison = record
      { left = Chosen.curry-computation; right = id₌ pr₂
      ; compatible = (comp₌-unitˡ-One desired ∙
          comp₌-cong (postWhisker-id₌ p pr₂) Chosen.matching-image) ⁻¹ }

    private
      composed : ConeIdentification₁
        (evaluated-cone (cone-restrict Chosen.factor L.fiber)) (family-cone F)
      composed = cone-compose encoded-comparison (evaluated-identification-One Chosen.computation)

    comparison : ConeIdentification₁
      (family-cone (L.evaluated-family Chosen.factor)) (family-cone F)
    comparison = record
      { left = Chosen.underlying-computation; right = id₌ pr₂
      ; compatible = replace-edges₌ (id₌ _)
          (postWhisker p ◁ comp₌-unitˡ-One (id₌ pr₂)) (ConeIdentification₁.compatible composed) }
```
