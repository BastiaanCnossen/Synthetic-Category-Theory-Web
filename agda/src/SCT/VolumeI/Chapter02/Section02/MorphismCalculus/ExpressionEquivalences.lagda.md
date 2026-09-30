# Equivalences of framed morphism expressions

This record packages two expression operations with comparison maps and
inverse laws. Its reflection lemmas use the inverse laws, with both
endpoint compatibility equations retained. It is a reusable interface,
not an additional axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I

record ExpressionEquivalence {Γ C D : CAT}
  (x₀ x₁ : MAP Γ C) (y₀ y₁ : MAP Γ D) : Set m where
  field
    forward : MorphismExpression x₀ x₁ → MorphismExpression y₀ y₁
    backward : MorphismExpression y₀ y₁ → MorphismExpression x₀ x₁
    forward-cong : {f g : MorphismExpression x₀ x₁} → ExpressionIso f g → ExpressionIso (forward f) (forward g)
    backward-cong : {f g : MorphismExpression y₀ y₁} → ExpressionIso f g → ExpressionIso (backward f) (backward g)
    backward-forward : (f : MorphismExpression x₀ x₁) → ExpressionIso (backward (forward f)) f
    forward-backward : (g : MorphismExpression y₀ y₁) → ExpressionIso (forward (backward g)) g

  reflect-forward : {f g : MorphismExpression x₀ x₁} → ExpressionIso (forward f) (forward g) → ExpressionIso f g
  reflect-forward {f} {g} α = expressionIso-compose (backward-forward g)
    (expressionIso-compose (backward-cong α) (expressionIso-inverse (backward-forward f)))

  reflect-backward : {f g : MorphismExpression y₀ y₁} → ExpressionIso (backward f) (backward g) → ExpressionIso f g
  reflect-backward {f} {g} α = expressionIso-compose (forward-backward g)
    (expressionIso-compose (forward-cong α) (expressionIso-inverse (forward-backward f)))
```
