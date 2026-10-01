# Comparing universal counits

A universal counit supplies a factorization of every morphism with the
specified target, and reflects comparisons between such factorizations.
Two universal counits have canonically inverse comparison expressions.
The calculation uses the derived opaque expression calculus. The adjunction
module supplies these counits by transporting the raw transposition laws
along the calculus comparison fields.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UniversalCounits
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
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit)

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionCalculus 𝒯 M ℱ P I E S Q using (ExpressionCalculus; expression-calculus)

module At (Γ : CAT) where
  open ExpressionCalculus (expression-calculus Γ) using ()
    renaming (identity to sealed-identity; composite to sealed-compose; post to sealed-post;
      composite-cong to sealed-cong; associative to sealed-associativity;
      unit-left to sealed-left-unit; post-unit to sealed-post-identity;
      post-composite to sealed-post-compose)

  record UniversalCounit {C D : CAT} (l : MAP C D) (y : MAP Γ D) (r : MAP Γ C) : Set m where
    field
      counit : MorphismExpression (l ∘ r) y
      factor : (x : MAP Γ C) → MorphismExpression (l ∘ x) y → MorphismExpression x r
      factor-law : (x : MAP Γ C) (f : MorphismExpression (l ∘ x) y) →
        ExpressionIso (sealed-compose (sealed-post l (factor x f)) counit) f
      reflect : {x : MAP Γ C} (f g : MorphismExpression x r) →
        ExpressionIso (sealed-compose (sealed-post l f) counit)
          (sealed-compose (sealed-post l g) counit) → ExpressionIso f g
  
  abstract
    round-trip : {C D : CAT} (l : MAP C D) {x x′ : MAP Γ C} {y : MAP Γ D}
      (ε : MorphismExpression (l ∘ x) y) (ε′ : MorphismExpression (l ∘ x′) y)
      (u : MorphismExpression x x′) (v : MorphismExpression x′ x) →
      ExpressionIso (sealed-compose (sealed-post l u) ε′) ε →
      ExpressionIso (sealed-compose (sealed-post l v) ε) ε′ →
      ExpressionIso (sealed-compose (sealed-post l (sealed-compose u v)) ε) ε
    round-trip l ε ε′ u v first second = expressionIso-compose first
      (expressionIso-compose (sealed-cong (expressionIso-id (sealed-post l u)) second)
        (expressionIso-compose (expressionIso-inverse (sealed-associativity (sealed-post l u) (sealed-post l v) ε))
          (sealed-cong (expressionIso-inverse (sealed-post-compose l u v)) (expressionIso-id ε))))
  
    identity-factor : {C D : CAT} (l : MAP C D) {x : MAP Γ C} {y : MAP Γ D}
      (ε : MorphismExpression (l ∘ x) y) →
      ExpressionIso (sealed-compose (sealed-post l (sealed-identity x)) ε) ε
    identity-factor l {x} ε = expressionIso-compose (sealed-left-unit ε)
      (sealed-cong (sealed-post-identity l x) (expressionIso-id ε))
  
  module Compare {C D : CAT} {l : MAP C D} {y : MAP Γ D} {x x′ : MAP Γ C}
    (a : UniversalCounit l y x) (b : UniversalCounit l y x′) where
    private
      module A = UniversalCounit a
      module B = UniversalCounit b
  
    forward : MorphismExpression x x′
    forward = B.factor x A.counit
  
    backward : MorphismExpression x′ x
    backward = A.factor x′ B.counit
  
    abstract
      backward-forward : ExpressionIso (sealed-compose forward backward) (sealed-identity x)
      backward-forward = A.reflect (sealed-compose forward backward) (sealed-identity x)
        (expressionIso-compose (expressionIso-inverse (identity-factor l A.counit))
          (round-trip l A.counit B.counit forward backward
            (B.factor-law x A.counit) (A.factor-law x′ B.counit)))
  
      forward-backward : ExpressionIso (sealed-compose backward forward) (sealed-identity x′)
      forward-backward = B.reflect (sealed-compose backward forward) (sealed-identity x′)
        (expressionIso-compose (expressionIso-inverse (identity-factor l B.counit))
          (round-trip l B.counit A.counit backward forward
            (A.factor-law x′ B.counit) (B.factor-law x A.counit)))
  
  
```