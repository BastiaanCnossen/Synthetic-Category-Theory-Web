# Chosen expression operations and their construction comparisons

Identity, composition and postcomposition are available before the laws of
associativity and units. This package keeps the chosen operations opaque while
retaining comparisons with their actual constructions. The full
`ExpressionCalculus` uses these same operations when adding their laws.
No commutative-square axiom is needed here.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionOperations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I

record ExpressionOperations (Γ : CAT) : Set (c ⊔ m) where
  field
    identity : {C : CAT} (x : MAP Γ C) → MorphismExpression x x
    composite : {C : CAT} {x y z : MAP Γ C} →
      MorphismExpression x y → MorphismExpression y z → MorphismExpression x z
    post : {C D : CAT} (F : MAP C D) {x y : MAP Γ C} →
      MorphismExpression x y → MorphismExpression (F ∘ x) (F ∘ y)
    identity-comparison : {C : CAT} (x : MAP Γ C) →
      ExpressionIso (identity x) (identity-expression x)
    composite-comparison : {C : CAT} {x y z : MAP Γ C}
      (f : MorphismExpression x y) (g : MorphismExpression y z) →
      ExpressionIso (composite f g) (compose-expression f g)
    post-comparison : {C D : CAT} (F : MAP C D) {x y : MAP Γ C}
      (f : MorphismExpression x y) → ExpressionIso (post F f) (post-expression F f)

opaque
  expression-operations : (Γ : CAT) → ExpressionOperations Γ
  expression-operations Γ = record
    { identity = identity-expression
    ; composite = compose-expression
    ; post = post-expression
    ; identity-comparison = λ x → expressionIso-id (identity-expression x)
    ; composite-comparison = λ f g → expressionIso-id (compose-expression f g)
    ; post-comparison = λ F f → expressionIso-id (post-expression F f)
    }
```
