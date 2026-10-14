# Naturality of recovered composition laws

Relative evaluation carries composition to ordinary functor composition.
The naturality squares for the recovered units and associator are obtained
by pasting these specified comparisons with ordinary functor naturality.
For the associator, the five known faces of a cube determine the sixth.
The input identification families have a common parameter X, independent
of their term source P. The recovered laws appear as constant sides over X.
Reflection requires only that P is an anima; X need not be an anima.
These statements concern the recovered laws, rather than their universal
specializations at arbitrary term sources.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CompositionNaturality where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization as Ordinary
  hiding (unitˡ-natural; unitʳ-natural; assoc-natural)
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (postWhisker-id; preWhisker-id)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
  using (FunctorOverBase)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (IdentificationOver)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (inverse-route-square)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-constant; pair⁼-cong)
import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors as Binary
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Composition
open import SCT.VolumeI.Chapter01.Section04.Currying using (uncurry⁼; uncurry⁼-constant)
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase
open import SCT.VolumeI.Chapter01.Section04.EvaluationCoherence
open import SCT.VolumeI.Chapter01.Section04.CompositionLaws
open import SCT.VolumeI.Chapter01.Section04.CompositionCoherence
  using (evaluation⁼-identity; evaluation⁼-composition)

module _ {Γ : Context} {P : CAT Γ} where
  open Terms.InContext P using (Term)

  private
    evaluated : {C D : CAT Γ} → Term (Map C D) → MAP (P × C) (P × D)
    evaluated x = FunctorOverBase.functor (evaluation-over x)

    comparison : {A B C : CAT Γ} (y : Term (Map B C)) (x : Term (Map A B))
      → evaluated (compose y x) =₁ (evaluated y ∘ evaluated x)
    comparison y x = IdentificationOver.identification (evaluation-compose y x)

    identity-comparison : (C : CAT Γ) → evaluated (identity-map C) =₁ id (P × C)
    identity-comparison C = IdentificationOver.identification (evaluation-identity P C)

    left-frame : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → evaluated (compose (compose z y) x) =₁ ((evaluated z ∘ evaluated y) ∘ evaluated x)
    left-frame z y x = (comparison z y ▷ evaluated x) ∙ comparison (compose z y) x

    right-frame : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → evaluated (compose z (compose y x)) =₁ (evaluated z ∘ (evaluated y ∘ evaluated x))
    right-frame z y x = (evaluated z ◁ comparison y x) ∙ comparison z (compose y x)

    associator-image : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → evaluated (compose (compose z y) x) =₁ evaluated (compose z (compose y x))
    associator-image z y x = IdentificationOver.identification (evaluation-assoc z y x)

    associator-square : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → SquareCell₌ (associator-image z y x) (comp-assoc (evaluated x) (evaluated y) (evaluated z))
          (left-frame z y x) (right-frame z y x)
    associator-square z y x = inverse-route-square (left-frame z y x)
      (evaluated z ◁ comparison y x) (comparison z (compose y x))
      (associator-image z y x) (comp-assoc (evaluated x) (evaluated y) (evaluated z)) (id₌ _)

```

Evaluation of a constant identification must retain the literal constant
identity in its first coordinate. The comparison below first evaluates the
uncurrying action on constants, then compares that coordinate with its
value at One. Pasted constant sides are normalized to the specified
composite sides, without replacing any recovered image.

```agda
  module RecoveredNaturality (pAn : isAn P) where
    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      private
        evaluation-constant : {C D : CAT Γ} {x y : Term (Map C D)} (α : x =₁ y)
          → evaluation⁼ (const {P = X} α) =₁ const (evaluation⁼ α)
        evaluation-constant α =
          const-cong (pair⁼-cong ((const-One (id₌ pr₁)) ⁻¹) (id₌ (uncurry⁼ α))) ∙
            (pair⁼-constant (id₌ pr₁) (uncurry⁼ α) ∙
              pair⁼-cong (id₌ (const (id₌ pr₁))) (uncurry⁼-constant α))

        paste-fixed : {C D : CAT Γ} {x y x′ y′ x″ y″ : MAP C D}
          {t : x ＝ y} {m : x′ ＝ y′} {b : x″ ＝ y″}
          {l₁ : x =₁ x′} {r₁ : y =₁ y′} {l₂ : x′ =₁ x″} {r₂ : y′ =₁ y″}
          → SquareCell₌ t m (const l₁) (const r₁)
          → SquareCell₌ m b (const l₂) (const r₂)
          → SquareCell₌ t b (const (l₂ ∙ l₁)) (const (r₂ ∙ r₁))
        paste-fixed {l₁ = l₁} {r₁} {l₂} {r₂} first second =
          replace-sides₌ (const-comp l₂ l₁) (const-comp r₂ r₁) (paste-square₌ first second)

        comparison-natural : {A B C : CAT Γ}
          {y y′ : Term (Map B C)} {x x′ : Term (Map A B)}
          (α : y ＝ y′) (β : x ＝ x′)
          → SquareCell₌ (evaluation⁼ (compose⁼ α β)) (evaluation⁼ α ⋆ evaluation⁼ β)
              (const (comparison y x)) (const (comparison y′ x′))
        comparison-natural = evaluation-compose-natural

        left-frame-natural : {A B C D : CAT Γ}
          {z z′ : Term (Map C D)} {y y′ : Term (Map B C)} {x x′ : Term (Map A B)}
          (γ : z ＝ z′) (β : y ＝ y′) (α : x ＝ x′)
          → SquareCell₌ (evaluation⁼ (compose⁼ (compose⁼ γ β) α))
              ((evaluation⁼ γ ⋆ evaluation⁼ β) ⋆ evaluation⁼ α)
              (const (left-frame z y x)) (const (left-frame z′ y′ x′))
        left-frame-natural {z = z} {z′} {y} {y′} {x} {x′} γ β α =
          paste-fixed (comparison-natural (compose⁼ γ β) α)
            (replace-sides₌ (pre-constant (comparison z y) (evaluated x))
              (pre-constant (comparison z′ y′) (evaluated x′))
              (hcomp-square₌-outer (comparison-natural γ β) (evaluation⁼ α)))

        right-frame-natural : {A B C D : CAT Γ}
          {z z′ : Term (Map C D)} {y y′ : Term (Map B C)} {x x′ : Term (Map A B)}
          (γ : z ＝ z′) (β : y ＝ y′) (α : x ＝ x′)
          → SquareCell₌ (evaluation⁼ (compose⁼ γ (compose⁼ β α)))
              (evaluation⁼ γ ⋆ (evaluation⁼ β ⋆ evaluation⁼ α))
              (const (right-frame z y x)) (const (right-frame z′ y′ x′))
        right-frame-natural {z = z} {z′} {y} {y′} {x} {x′} γ β α =
          paste-fixed (comparison-natural γ (compose⁼ β α))
            (replace-sides₌ (post-constant (evaluated z) (comparison y x))
              (post-constant (evaluated z′) (comparison y′ x′))
              (hcomp-square₌-inner (comparison-natural β α) (evaluation⁼ γ)))

        associator-natural-image : {A B C D : CAT Γ}
          {z z′ : Term (Map C D)} {y y′ : Term (Map B C)} {x x′ : Term (Map A B)}
          (γ : z ＝ z′) (β : y ＝ y′) (α : x ＝ x′)
          → SquareCell₌ (const (associator-image z y x)) (const (associator-image z′ y′ x′))
              (evaluation⁼ (compose⁼ (compose⁼ γ β) α))
              (evaluation⁼ (compose⁼ γ (compose⁼ β α)))
        associator-natural-image {z = z} {z′} {y} {y′} {x} {x′} γ β α =
          fill-cube₌ (constant-square₌ (associator-square z y x))
            (constant-square₌ (associator-square z′ y′ x′))
            (transpose-square₌ (left-frame-natural γ β α))
            (transpose-square₌ (right-frame-natural γ β α))
            (Ordinary.assoc-natural (evaluation⁼ γ) (evaluation⁼ β) (evaluation⁼ α))

        left-unit-natural-image : {C D : CAT Γ} {x x′ : Term (Map C D)} (α : x ＝ x′)
          → SquareCell₌ (evaluation⁼ (compose⁼ (const (id₌ (identity-map D))) α)) (evaluation⁼ α)
              (const (IdentificationOver.identification (evaluation-unitˡ x)))
              (const (IdentificationOver.identification (evaluation-unitˡ x′)))
        left-unit-natural-image {D = D} {x} {x′} α =
          let J = evaluated (identity-map D)
              ε = identity-comparison D
              z = evaluation⁼ α
              first = replace-edges₌ (id₌ _)
                (hcomp-id-outer J z ∙ hcomp-cong (evaluation⁼-identity (identity-map D)) (id₌ z))
                (comparison-natural (const (id₌ (identity-map D))) α)
          in paste-fixed (paste-fixed first (interchange-fixedOuter ε z)) (postWhisker-id z)

        right-unit-natural-image : {C D : CAT Γ} {x x′ : Term (Map C D)} (α : x ＝ x′)
          → SquareCell₌ (evaluation⁼ (compose⁼ α (const (id₌ (identity-map C))))) (evaluation⁼ α)
              (const (IdentificationOver.identification (evaluation-unitʳ x)))
              (const (IdentificationOver.identification (evaluation-unitʳ x′)))
        right-unit-natural-image {C = C} {x = x} {x′} α =
          let J = evaluated (identity-map C)
              ε = identity-comparison C
              z = evaluation⁼ α
              first = replace-edges₌ (id₌ _)
                (hcomp-id-inner z J ∙ hcomp-cong (id₌ z) (evaluation⁼-identity (identity-map C)))
                (comparison-natural α (const (id₌ (identity-map C))))
          in paste-fixed (paste-fixed first ((interchange-fixedInner z ε) ⁻¹)) (preWhisker-id z)

      private
        constant-image : {C D : CAT Γ} {x y : Term (Map C D)}
          (a : x =₁ y) (r : evaluated x =₁ evaluated y)
          → evaluation⁼ a =₂ r → evaluation⁼ (const {P = X} a) =₁ const r
        constant-image a r image = const-cong image ∙ evaluation-constant a

        reflect-square : {C D : CAT Γ} {x y x′ y′ : Term (Map C D)}
          (a : x =₁ y) (a′ : x′ =₁ y′) (s : x ＝ x′) (t : y ＝ y′)
          (r : evaluated x =₁ evaluated y) (r′ : evaluated x′ =₁ evaluated y′)
          → evaluation⁼ a =₂ r → evaluation⁼ a′ =₂ r′
          → SquareCell₌ (evaluation⁼ s) (evaluation⁼ t) (const r) (const r′)
          → SquareCell₌ s t (const a) (const a′)
        reflect-square a a′ s t r r′ image image′ square =
          let source-image = constant-image a r image
              target-image = constant-image a′ r′ image′
          in evaluation⁼-reflect pAn _ _
            ((evaluation⁼-composition t (const a)) ⁻¹ ∙
            (comp₌-cong (id₌ (evaluation⁼ t)) (source-image ⁻¹) ∙
            (square ∙
            (comp₌-cong target-image (id₌ (evaluation⁼ s)) ∙
              evaluation⁼-composition (const a′) s))))

      unitˡ-natural : {C D : CAT Γ} {x x′ : Term (Map C D)} (α : x ＝ x′)
        → SquareCell₌ (compose⁼ (const (id₌ (identity-map D))) α) α
            (const (Recovered.unitˡ pAn x)) (const (Recovered.unitˡ pAn x′))
      unitˡ-natural {x = x} {x′} α = reflect-square _ _ _ _ _ _
        (Recovered.unitˡ-image pAn x) (Recovered.unitˡ-image pAn x′) (left-unit-natural-image α)

      unitʳ-natural : {C D : CAT Γ} {x x′ : Term (Map C D)} (α : x ＝ x′)
        → SquareCell₌ (compose⁼ α (const (id₌ (identity-map C)))) α
            (const (Recovered.unitʳ pAn x)) (const (Recovered.unitʳ pAn x′))
      unitʳ-natural {x = x} {x′} α = reflect-square _ _ _ _ _ _
        (Recovered.unitʳ-image pAn x) (Recovered.unitʳ-image pAn x′) (right-unit-natural-image α)

      assoc-natural : {A B C D : CAT Γ}
        {z z′ : Term (Map C D)} {y y′ : Term (Map B C)} {x x′ : Term (Map A B)}
        (γ : z ＝ z′) (β : y ＝ y′) (α : x ＝ x′)
        → SquareCell₌ (compose⁼ (compose⁼ γ β) α) (compose⁼ γ (compose⁼ β α))
            (const (Recovered.assoc pAn z y x)) (const (Recovered.assoc pAn z′ y′ x′))
      assoc-natural {z = z} {z′} {y} {y′} {x} {x′} γ β α = reflect-square _ _ _ _ _ _
        (Recovered.assoc-image pAn z y x) (Recovered.assoc-image pAn z′ y′ x′)
        (transpose-square₌ (associator-natural-image γ β α))
```

At One, normalize the fixed identity inputs and the constant law sides.
These individual statements are adapters to the family proofs.

```agda
    unitˡ-natural-One : {C D : CAT Γ} {x x′ : Term (Map C D)} (α : x =₁ x′)
      → SquareCell₌ (compose⁼ (id₌ (identity-map D)) α) α
          (Recovered.unitˡ pAn x) (Recovered.unitˡ pAn x′)
    unitˡ-natural-One {D = D} α = unconst-sides₌
      (replace-edges₌ (Binary.binary-cong₂ mapComp (const-One (id₌ (identity-map D))) (id₌ α))
        (id₌ α) (unitˡ-natural α))

    unitʳ-natural-One : {C D : CAT Γ} {x x′ : Term (Map C D)} (α : x =₁ x′)
      → SquareCell₌ (compose⁼ α (id₌ (identity-map C))) α
          (Recovered.unitʳ pAn x) (Recovered.unitʳ pAn x′)
    unitʳ-natural-One {C = C} α = unconst-sides₌
      (replace-edges₌ (Binary.binary-cong₂ mapComp (id₌ α) (const-One (id₌ (identity-map C))))
        (id₌ α) (unitʳ-natural α))

    assoc-natural-One : {A B C D : CAT Γ}
      {z z′ : Term (Map C D)} {y y′ : Term (Map B C)} {x x′ : Term (Map A B)}
      (γ : z =₁ z′) (β : y =₁ y′) (α : x =₁ x′)
      → SquareCell₌ (compose⁼ (compose⁼ γ β) α) (compose⁼ γ (compose⁼ β α))
          (Recovered.assoc pAn z y x) (Recovered.assoc pAn z′ y′ x′)
    assoc-natural-One γ β α = unconst-sides₌ (assoc-natural γ β α)
```
