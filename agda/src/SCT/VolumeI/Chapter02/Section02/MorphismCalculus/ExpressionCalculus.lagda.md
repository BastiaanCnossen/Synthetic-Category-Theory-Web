# Opaque expression calculus with comparisons to its constructions

The package adds checked laws to the opaque operations of `ExpressionOperations`.
Its outer record is transparent so formula modules and law modules use one
chosen set of operations. The operations themselves remain opaque; only the
realization of their laws unfolds them. Construction comparisons retain the
connection to Segal composition and postcomposition. No extra axiom is assumed.

The package also supplies derived comparison laws: postcomposition acts on
comparisons, a specified comparison of middle composites can be applied
inside a fourfold composite, and iterated postcomposition preserves composition. These laws use an
arbitrary instance of the calculus; they do not belong to an adjunction proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E
  using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity 𝒯 M ℱ P I E S Q
  using (associativity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)

import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionOperations as Operations

record ExpressionCalculus (Γ : CAT) : Set (c ⊔ m) where
  field
    identity : {C : CAT} (x : MAP Γ C) → MorphismExpression x x
    composite : {C : CAT} {x y z : MAP Γ C} →
      MorphismExpression x y → MorphismExpression y z → MorphismExpression x z
    post : {C D : CAT} (F : MAP C D) {x y : MAP Γ C} →
      MorphismExpression x y → MorphismExpression (F ∘ x) (F ∘ y)
    composite-cong : {C : CAT} {x y z : MAP Γ C}
      {f f′ : MorphismExpression x y} {g g′ : MorphismExpression y z} →
      ExpressionIso f f′ → ExpressionIso g g′ → ExpressionIso (composite f g) (composite f′ g′)
    associative : {C : CAT} {w x y z : MAP Γ C}
      (f : MorphismExpression w x) (g : MorphismExpression x y) (h : MorphismExpression y z) →
      ExpressionIso (composite f (composite g h)) (composite (composite f g) h)
    unit-left : {C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
      ExpressionIso (composite (identity x) f) f
    unit-right : {C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
      ExpressionIso (composite f (identity y)) f
    post-unit : {C D : CAT} (F : MAP C D) (x : MAP Γ C) →
      ExpressionIso (post F (identity x)) (identity (F ∘ x))
    post-composite : {C D : CAT} (F : MAP C D) {x y z : MAP Γ C}
      (f : MorphismExpression x y) (g : MorphismExpression y z) →
      ExpressionIso (composite (post F f) (post F g)) (post F (composite f g))
    identity-comparison : {C : CAT} (x : MAP Γ C) →
      ExpressionIso (identity x) (identity-expression x)
    composite-comparison : {C : CAT} {x y z : MAP Γ C}
      (f : MorphismExpression x y) (g : MorphismExpression y z) →
      ExpressionIso (composite f g) (compose-expression f g)
    post-comparison : {C D : CAT} (F : MAP C D) {x y : MAP Γ C}
      (f : MorphismExpression x y) → ExpressionIso (post F f) (post-expression F f)

    action-comparison : {C D : CAT} (F : MAP C D) {x x′ : MAP Γ C} {y : MAP Γ D}
      (f : MorphismExpression x x′) (g : MorphismExpression (F ∘ x′) y) →
      ExpressionIso (composite (post F f) g) (compose-expression (post-expression F f) g)
    inverse-law : {C : CAT} {x y : MAP Γ C}
      (f : MorphismExpression x y) (g : MorphismExpression y x) →
      ExpressionIso (composite f g) (identity x) →
      ExpressionIso (compose-expression f g) (identity-expression x)

  abstract
    post-cong : {C D : CAT} (F : MAP C D) {x y : MAP Γ C}
      {u v : MorphismExpression x y} → ExpressionIso u v → ExpressionIso (post F u) (post F v)
    post-cong F {u = u} {v} same = expressionIso-compose (expressionIso-inverse (post-comparison F v))
      (expressionIso-compose (post-expressionIso F same) (post-comparison F u))

    post-comparison-twice : {B C D : CAT} (F : MAP B C) (G : MAP C D)
      {x y : MAP Γ B} (u : MorphismExpression x y) →
      ExpressionIso (post G (post F u)) (post-expression G (post-expression F u))
    post-comparison-twice F G u = expressionIso-compose (post-expressionIso G (post-comparison F u))
      (post-comparison G (post F u))

    composite-middle : {C : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP Γ C}
      (a₀ : MorphismExpression x₀ x₁) (b₀ : MorphismExpression x₁ x₂)
      (c₀ : MorphismExpression x₂ x₃) (d₀ : MorphismExpression x₃ x₄) →
      ExpressionIso (composite (composite a₀ b₀) (composite c₀ d₀))
        (composite a₀ (composite (composite b₀ c₀) d₀))
    composite-middle a₀ b₀ c₀ d₀ = expressionIso-compose
      (composite-cong (expressionIso-id a₀) (associative b₀ c₀ d₀))
      (expressionIso-inverse (associative a₀ b₀ (composite c₀ d₀)))

    composite-exchange : {C : CAT} {x₀ x₁ x₂ x₃ x₄ x₂′ : MAP Γ C}
      (a₀ : MorphismExpression x₀ x₁) (b₀ : MorphismExpression x₁ x₂)
      (c₀ : MorphismExpression x₂ x₃) (d₀ : MorphismExpression x₃ x₄)
      (c₁ : MorphismExpression x₁ x₂′) (b₁ : MorphismExpression x₂′ x₃) →
      ExpressionIso (composite b₀ c₀) (composite c₁ b₁) →
      ExpressionIso (composite (composite a₀ b₀) (composite c₀ d₀))
        (composite (composite a₀ c₁) (composite b₁ d₀))
    composite-exchange a₀ b₀ c₀ d₀ c₁ b₁ same = expressionIso-compose
      (expressionIso-inverse (composite-middle a₀ c₁ b₁ d₀))
      (expressionIso-compose
        (composite-cong (expressionIso-id a₀) (composite-cong same (expressionIso-id d₀)))
        (composite-middle a₀ b₀ c₀ d₀))

    post-composite-twice : {B C D : CAT} (F : MAP B C) (G : MAP C D)
      {x y z : MAP Γ B} (u : MorphismExpression x y) (v : MorphismExpression y z) →
      ExpressionIso (post G (post F (composite u v)))
        (composite (post G (post F u)) (post G (post F v)))
    post-composite-twice F G u v = expressionIso-compose
      (expressionIso-inverse (post-composite G (post F u) (post F v)))
      (post-cong G (expressionIso-inverse (post-composite F u v)))

private
  module ChosenLaws (Γ : CAT) where
    module O = Operations.ExpressionOperations (Operations.expression-operations 𝒯 M ℱ P I E S Γ)

    opaque
      unfolding Operations.expression-operations
      composite-cong : {C : CAT} {x y z : MAP Γ C}
        {f f′ : MorphismExpression x y} {g g′ : MorphismExpression y z} →
        ExpressionIso f f′ → ExpressionIso g g′ → ExpressionIso (O.composite f g) (O.composite f′ g′)
      composite-cong = compose-expression-cong

      associative : {C : CAT} {w x y z : MAP Γ C}
        (f : MorphismExpression w x) (g : MorphismExpression x y) (h : MorphismExpression y z) →
        ExpressionIso (O.composite f (O.composite g h)) (O.composite (O.composite f g) h)
      associative = associativity

      unit-left : {C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
        ExpressionIso (O.composite (O.identity x) f) f
      unit-left = left-unit

      unit-right : {C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
        ExpressionIso (O.composite f (O.identity y)) f
      unit-right = right-unit

      post-unit : {C D : CAT} (F : MAP C D) (x : MAP Γ C) →
        ExpressionIso (O.post F (O.identity x)) (O.identity (F ∘ x))
      post-unit = post-identity

      post-composite : {C D : CAT} (F : MAP C D) {x y z : MAP Γ C}
        (f : MorphismExpression x y) (g : MorphismExpression y z) →
        ExpressionIso (O.composite (O.post F f) (O.post F g)) (O.post F (O.composite f g))
      post-composite = post-composition

      action-comparison : {C D : CAT} (F : MAP C D) {x x′ : MAP Γ C} {y : MAP Γ D}
        (f : MorphismExpression x x′) (g : MorphismExpression (F ∘ x′) y) →
        ExpressionIso (O.composite (O.post F f) g) (compose-expression (post-expression F f) g)
      action-comparison = λ F f g → expressionIso-id (compose-expression (post-expression F f) g)

      inverse-law : {C : CAT} {x y : MAP Γ C}
        (f : MorphismExpression x y) (g : MorphismExpression y x) →
        ExpressionIso (O.composite f g) (O.identity x) →
        ExpressionIso (compose-expression f g) (identity-expression x)
      inverse-law = λ f g law → law

expression-calculus : (Γ : CAT) → ExpressionCalculus Γ
expression-calculus Γ = record
  { identity = O.identity
  ; composite = O.composite
  ; post = O.post
  ; composite-cong = L.composite-cong
  ; associative = L.associative
  ; unit-left = L.unit-left
  ; unit-right = L.unit-right
  ; post-unit = L.post-unit
  ; post-composite = L.post-composite
  ; action-comparison = L.action-comparison
  ; inverse-law = L.inverse-law
  ; identity-comparison = O.identity-comparison
  ; composite-comparison = O.composite-comparison
  ; post-comparison = O.post-comparison
  }
  where
  module O = Operations.ExpressionOperations (Operations.expression-operations 𝒯 M ℱ P I E S Γ)
  module L = ChosenLaws Γ
```
