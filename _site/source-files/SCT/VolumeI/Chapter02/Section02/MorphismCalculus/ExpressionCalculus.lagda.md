# Opaque expression calculus with comparisons to its constructions

The package is constructed from the existing framed-expression operations
and their checked laws. Its operation fields stay opaque in downstream
algebra, while the comparison fields retain the connection to the actual
Segal composition and postcomposition. No extra axiom is assumed.

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
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E
  using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity 𝒯 M ℱ P I E S Q
  using (associativity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)

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
  expression-calculus : (Γ : CAT) → ExpressionCalculus Γ
  expression-calculus Γ = record
    { identity = identity-expression
    ; composite = compose-expression
    ; post = post-expression
    ; composite-cong = compose-expression-cong
    ; associative = associativity
    ; unit-left = left-unit
    ; unit-right = right-unit
    ; post-unit = post-identity
    ; post-composite = post-composition
    ; identity-comparison = λ x → expressionIso-id (identity-expression x)
    ; composite-comparison = λ f g → expressionIso-id (compose-expression f g)
    ; action-comparison = λ F f g → expressionIso-id (compose-expression (post-expression F f) g)
    ; inverse-law = λ f g law → law
    ; post-comparison = λ F f → expressionIso-id (post-expression F f)
    }
```