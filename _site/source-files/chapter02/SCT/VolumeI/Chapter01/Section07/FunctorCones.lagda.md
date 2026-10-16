# Native evaluation of whole cones

Uncurrying transports a cone's specified matching along the actual
postcomposition evaluation triangles. Its action on complete cone
identifications preserves that matching square for an independent family
parameter. Currying recovers the matching through the same native action.
No pullback preservation is assumed or claimed by these constructions.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.FunctorCones where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-compose; cone-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section07.Functoriality

private
  module _ {Γ : Context} {X A B : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    constant-endpoints : {x x′ y y′ : MAP A B}
      (p : x =₁ x′) (q : y =₁ y′) (α : x =₁ y)
      → changeEndpoints (const {P = X} p) (const q) (const α) =₁ const (changeEndpoints p q α)
    constant-endpoints p q α = const-comp q (α ∙ p ⁻¹) ∙
      comp₌-cong (id₌ (const q))
        (const-comp α (p ⁻¹) ∙ comp₌-cong (id₌ (const α)) ((const-inv p) ⁻¹))

  module _ {Γ : Context} {X F K D T : CAT Γ} (e : MAP (F × K) D) where
    open Terms.Equalities X using (_＝_)

    evaluation-square : {f g f′ g′ : MAP T F}
      {α : f ＝ g} {β : f′ ＝ g′} {p : f ＝ f′} {q : g ＝ g′}
      → SquareCell₌ α β p q
      → SquareCell₌ (evaluate⁼ e α) (evaluate⁼ e β) (evaluate⁼ e p) (evaluate⁼ e q)
    evaluation-square {α = α} {β} {p} {q} square = evaluate⁼-composition e β p ∙
      (evaluate⁼-cong e square ∙ (evaluate⁼-composition e q α) ⁻¹)

    evaluation-fixed-square : {f g f′ g′ : MAP T F}
      {α : f ＝ g} {β : f′ ＝ g′} {p : f =₁ f′} {q : g =₁ g′}
      → SquareCell₌ α β (const p) (const q)
      → SquareCell₌ (evaluate⁼ e α) (evaluate⁼ e β) (const (evaluate-cong e p)) (const (evaluate-cong e q))
    evaluation-fixed-square {p = p} {q} square =
      replace-sides₌ (evaluate⁼-constant e p) (evaluate⁼-constant e q) (evaluation-square square)

module FunctorCones {Γ : Context} (K : CAT Γ) {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) where
  private
    F = funPost {C = K} f
    G = funPost {C = K} g
    eC : MAP (Fun K C × K) C
    eC = funEval {C = K} {D = C}
    eD : MAP (Fun K D × K) D
    eD = funEval {C = K} {D = D}
    eE : MAP (Fun K E × K) E
    eE = funEval {C = K} {D = E}

  uncurryCone : {T : CAT Γ} → Cone F G T → Cone f g (T × K)
  uncurryCone s = record
    { left = evaluate eC (Cone.left s)
    ; right = evaluate eD (Cone.right s)
    ; match = changeEndpoints (funPost-uncurry f (Cone.left s)) (funPost-uncurry g (Cone.right s))
        (evaluate-cong eE (Cone.match s)) }

  uncurryCone-identification : {X T : CAT Γ} {s t : Cone F G T}
    → ConeIdentification X s t → ConeIdentification X (uncurryCone s) (uncurryCone t)
  uncurryCone-identification {s = s} {t} Φ = record
    { left = evaluate⁼ eC (ConeIdentification.left Φ)
    ; right = evaluate⁼ eD (ConeIdentification.right Φ)
    ; compatible = replace-sides₌
        (constant-endpoints (funPost-uncurry f (Cone.left s)) (funPost-uncurry g (Cone.right s))
          (evaluate-cong eE (Cone.match s)))
        (constant-endpoints (funPost-uncurry f (Cone.left t)) (funPost-uncurry g (Cone.right t))
          (evaluate-cong eE (Cone.match t)))
        (transport-square
          (const (funPost-uncurry f (Cone.left s))) (const (funPost-uncurry f (Cone.left t)))
          (const (funPost-uncurry g (Cone.right s))) (const (funPost-uncurry g (Cone.right t)))
          (const (evaluate-cong eE (Cone.match s))) (const (evaluate-cong eE (Cone.match t)))
          (evaluate⁼ eE (F ◁ ConeIdentification.left Φ)) (evaluate⁼ eE (G ◁ ConeIdentification.right Φ))
          (f ◁ evaluate⁼ eC (ConeIdentification.left Φ)) (g ◁ evaluate⁼ eD (ConeIdentification.right Φ))
          (funPost-uncurry-inputs f (ConeIdentification.left Φ))
          (funPost-uncurry-inputs g (ConeIdentification.right Φ))
          (evaluation-fixed-square eE (ConeIdentification.compatible Φ))) }

  module CurriedCone {T : CAT Γ} (s : Cone f g (T × K)) where
    left : MAP T (Fun K C)
    left = funCurry {C = K} {D = C} (Cone.left s)
    right : MAP T (Fun K D)
    right = funCurry {C = K} {D = D} (Cone.right s)
    left-β : evaluate eC left =₁ Cone.left s
    left-β = funCurry-β {C = K} {D = C} (Cone.left s)
    right-β : evaluate eD right =₁ Cone.right s
    right-β = funCurry-β {C = K} {D = D} (Cone.right s)

    wanted : Cone f g (T × K)
    wanted = cone-change-legs s (evaluate eC left) (evaluate eD right) (left-β ⁻¹) (right-β ⁻¹)
    desired = Cone.match wanted
    leftChange = funPost-uncurry f left
    rightChange = funPost-uncurry g right
    rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

    value : Cone F G T
    value = record
      { left = left; right = right
      ; match = reflect eE (funUniversal K E) (F ∘ left) (G ∘ right) rawMatch }

    match-β : Cone.match (uncurryCone value) =₂ desired
    match-β = restore-boundaries leftChange rightChange desired
      (evaluate-cong eE (Cone.match value))
      (reflect-β-One eE (funUniversal K E) (F ∘ left) (G ∘ right) rawMatch)

    comparison : ConeIdentification₁ (uncurryCone value) s
    comparison = cone-compose
      (cone-inverse (cone-change-legs-β s (evaluate eC left) (evaluate eD right) (left-β ⁻¹) (right-β ⁻¹)))
      (cone-retarget-match-identification (uncurryCone value) desired match-β)
```

## Recovering complete comparisons

Recover the two leg families through their actual native actions. The
supplied matching square is transported back along the postcomposition
evaluation squares. Higher recovery factors that exact square through the
native action and retains its image triangle. No equality of entire cone
identification witnesses is inferred merely from equality of their legs.

```agda
  module ReflectedCone {X T : CAT Γ} (s t : Cone F G T)
    (Φ : ConeIdentification X (uncurryCone s) (uncurryCone t)) where
    open Terms.Equalities X using (_＝_)

    left : Cone.left s ＝ Cone.left t
    left = reflect eC (funUniversal K C) (Cone.left s) (Cone.left t) (ConeIdentification.left Φ)
    right : Cone.right s ＝ Cone.right t
    right = reflect eD (funUniversal K D) (Cone.right s) (Cone.right t) (ConeIdentification.right Φ)
    left-image : evaluate⁼ eC left =₁ ConeIdentification.left Φ
    left-image = reflect-β eC (funUniversal K C) (Cone.left s) (Cone.left t) (ConeIdentification.left Φ)
    right-image : evaluate⁼ eD right =₁ ConeIdentification.right Φ
    right-image = reflect-β eD (funUniversal K D) (Cone.right s) (Cone.right t) (ConeIdentification.right Φ)

    private
      rawLeft = evaluate⁼ eE (F ◁ left)
      rawRight = evaluate⁼ eE (G ◁ right)
      targetLeft = f ◁ evaluate⁼ eC left
      targetRight = g ◁ evaluate⁼ eD right

      transported : SquareCell₌ targetLeft targetRight
        (changeEndpoints (const (funPost-uncurry f (Cone.left s))) (const (funPost-uncurry g (Cone.right s)))
          (const (evaluate-cong eE (Cone.match s))))
        (changeEndpoints (const (funPost-uncurry f (Cone.left t))) (const (funPost-uncurry g (Cone.right t)))
          (const (evaluate-cong eE (Cone.match t))))
      transported = replace-sides₌
        ((constant-endpoints (funPost-uncurry f (Cone.left s)) (funPost-uncurry g (Cone.right s))
          (evaluate-cong eE (Cone.match s))) ⁻¹)
        ((constant-endpoints (funPost-uncurry f (Cone.left t)) (funPost-uncurry g (Cone.right t))
          (evaluate-cong eE (Cone.match t))) ⁻¹)
        (replace-edges₌ ((postWhisker f ◁ left-image) ⁻¹) ((postWhisker g ◁ right-image) ⁻¹)
          (ConeIdentification.compatible Φ))

      native-square : SquareCell₌ rawLeft rawRight
        (const (evaluate-cong eE (Cone.match s))) (const (evaluate-cong eE (Cone.match t)))
      native-square = reflect-transported-square
        (const (funPost-uncurry f (Cone.left s))) (const (funPost-uncurry g (Cone.right s)))
        (const (funPost-uncurry f (Cone.left t))) (const (funPost-uncurry g (Cone.right t)))
        (const (evaluate-cong eE (Cone.match s))) (const (evaluate-cong eE (Cone.match t)))
        rawLeft rawRight targetLeft targetRight
        (funPost-uncurry-inputs f left) (funPost-uncurry-inputs g right) transported

    source-boundary = const (Cone.match t) ∙ (F ◁ left)
    target-boundary = (G ◁ right) ∙ const (Cone.match s)

    private
      source-image : evaluate⁼ eE source-boundary =₁
        (const (evaluate-cong eE (Cone.match t)) ∙ rawLeft)
      source-image = comp₌-cong (evaluate⁼-constant eE (Cone.match t)) (id₌ rawLeft) ∙
        evaluate⁼-composition eE (const (Cone.match t)) (F ◁ left)
      target-image : evaluate⁼ eE target-boundary =₁
        (rawRight ∙ const (evaluate-cong eE (Cone.match s)))
      target-image = comp₌-cong (id₌ rawRight) (evaluate⁼-constant eE (Cone.match s)) ∙
        evaluate⁼-composition eE (G ◁ right) (const (Cone.match s))
      image : evaluate⁼ eE source-boundary =₁ evaluate⁼ eE target-boundary
      image = target-image ⁻¹ ∙ (native-square ∙ source-image)

    native-action = evaluation-action eE (F ∘ Cone.left s) (G ∘ Cone.right t)

    wanted-image : (native-action ∘ source-boundary) =₁ (native-action ∘ target-boundary)
    wanted-image = (evaluation-action-evaluate eE target-boundary) ⁻¹ ∙
      (image ∙ evaluation-action-evaluate eE source-boundary)

    matching-factor : Fact.Factorization (postWhisker native-action) wanted-image
    matching-factor = evaluation-reflection₂ eE (funUniversal K E) source-boundary target-boundary wanted-image

    compatible : SquareCell₌ (F ◁ left) (G ◁ right) (const (Cone.match s)) (const (Cone.match t))
    compatible = Fact.factor matching-factor

    matching-image : (postWhisker native-action ∘ compatible) =₁ wanted-image
    matching-image = Fact.triangle matching-factor

    value : ConeIdentification X s t
    value = record { left = left; right = right; compatible = compatible }

  curry-uncurryCone : {T : CAT Γ} (s : Cone F G T)
    → ConeIdentification₁ (CurriedCone.value (uncurryCone s)) s
  curry-uncurryCone s = cone-identification-One
    (ReflectedCone.value (CurriedCone.value (uncurryCone s)) s
      (cone-identification (CurriedCone.comparison (uncurryCone s))))
```
