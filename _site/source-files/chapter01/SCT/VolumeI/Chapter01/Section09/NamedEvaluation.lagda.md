# Evaluation of a named structural functor

A named structural functor evaluated along an arbitrary terminal coordinate
has a fixed underlying family. Its complete square in an independently
indexed change of that coordinate is the prerequisite for relative family
comparisons. The operation retains the literal selected naming computation.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.NamedEvaluation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; preWhisker-id₌; comp-unitˡ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluate-restrict-substitution)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName; funName-β)

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

module NamedEvaluation {Γ : Context} {C S : CAT Γ} (p : MAP C S) where
  private
    eS : MAP (Fun C S × C) S
    eS = funEval {C = C} {D = S}
    point : MAP One (Fun C S)
    point = funName p

  named-evaluation : {K : CAT Γ} (z : MAP K One)
    → evaluate eS (point ∘ z) =₁ (p ∘ pr₂ {C = K} {D = C})
  named-evaluation z =
    (p ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (z ∘ pr₁) (id C ∘ pr₂))) ∙
      (comp-assoc (productMap z (id C)) (pr₂ {C = One} {D = C}) p ∙
        ((funName-β p ▷ productMap z (id C)) ∙ evaluate-restrict eS point z))

  module _ {X K : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    abstract
      named-evaluation-inputs : {z z′ : MAP K One} (δ : z ＝ z′)
        → SquareCell₌ (evaluate⁼ eS (point ◁ δ)) (const (id₌ (p ∘ pr₂ {C = K} {D = C})))
            (const (named-evaluation z)) (const (named-evaluation z′))
      named-evaluation-inputs {z} {z′} δ =
        replace-sides₌ (const-cong (normal z)) (const-cong (normal z′))
          (paste-fixed (evaluate-restrict-substitution eS point δ)
            (paste-fixed (interchange-fixedOuter (funName-β p) change) projected))
        where
        change : productMap z (id C) ＝ productMap z′ (id C)
        change = productMap-cong δ (const (id₌ (id C)))
        projection : (w : MAP K One) → (pr₂ {C = One} {D = C} ∘ productMap w (id C)) =₁ pr₂ {C = K} {D = C}
        projection z = comp-unitˡ pr₂ ∙ pair-β₂ (z ∘ pr₁) (id C ∘ pr₂)
        reduce : (const {P = X} (id₌ (id C)) ▷ pr₂ {C = K} {D = C}) =₁
          const {P = X} (id₌ (id C ∘ pr₂ {C = K} {D = C}))
        reduce = const-cong {X = X} (preWhisker-id₌ (id C) (pr₂ {C = K} {D = C})) ∙
          pre-constant {A = X} (id₌ (id C)) (pr₂ {C = K} {D = C})
        projection-square : SquareCell₌ (pr₂ {C = One} {D = C} ◁ change)
          (const {P = X} (id₌ (pr₂ {C = K} {D = C})))
          (const (projection z)) (const (projection z′))
        projection-square = paste-fixed
          (replace-edges₌ (id₌ (pr₂ {C = One} {D = C} ◁ change)) reduce
            (productMap-cong-triangle₂ δ (const (id₌ (id C)))))
          (transpose-square₌ (identity-square₌ (const {P = X} (comp-unitˡ (pr₂ {C = K} {D = C})))))
        projected : SquareCell₌ ((p ∘ pr₂ {C = One} {D = C}) ◁ change)
          (const (id₌ (p ∘ pr₂ {C = K} {D = C})))
          (const (post-triangle p pr₂ (productMap z (id C)) (projection z)))
          (const (post-triangle p pr₂ (productMap z′ (id C)) (projection z′)))
        projected = replace-edges₌ (id₌ _) (const-cong (postWhisker-id₌ p pr₂) ∙ post-constant p (id₌ pr₂))
          (post-triangle-inner p pr₂ change (const (id₌ pr₂)) (projection z) (projection z′) projection-square)
        normal : (w : MAP K One) →
          ((post-triangle p pr₂ (productMap w (id C)) (projection w) ∙
            (funName-β p ▷ productMap w (id C))) ∙ evaluate-restrict eS point w) =₂ named-evaluation w
        normal w = comp₌-assoc (p ◁ projection w)
          (comp-assoc (productMap w (id C)) pr₂ p)
          ((funName-β p ▷ productMap w (id C)) ∙ evaluate-restrict eS point w) ∙
          comp₌-assoc (post-triangle p pr₂ (productMap w (id C)) (projection w))
            (funName-β p ▷ productMap w (id C)) (evaluate-restrict eS point w)

```
