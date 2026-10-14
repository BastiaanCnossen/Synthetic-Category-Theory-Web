# Functors with a retraction reflect invertible expressions

If `g f` is identified with the identity functor, postcompose an inverse
of `f α` by `g`. Pasting the two postcompositions and then applying the
identity-functor comparison transports the inverse equations back to
`α`. The result holds over any absolute parameter category and retains
both endpoint frames.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.RetractionsReflectInverses
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions 𝒯 M ℱ P I E
  using (post-id)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting

module WithRetraction {C D : CAT} (f : MAP C D) (g : MAP D C)
  (η : (g ∘ f) =₁ id C) where

  reflect-invertible : {Γ : CAT} {x y : MAP Γ C} (α : MorphismExpression x y) →
    IsInvertibleExpression (post-expression f α) → IsInvertibleExpression α
  reflect-invertible {x = x} {y} α w = identified-invertible (post-id α)
    (retarget-invertible (post-expression (id C) α) (comp-unitˡ x) (comp-unitˡ y)
      (identified-invertible Paste.comparison
        (retarget-invertible (post-expression g (post-expression f α))
          Paste.source-change Paste.target-change (post-invertible g (post-expression f α) w))))
    where
    module Paste = Pasting.At 𝒯 M ℱ P I E f g (id C) η α
      using (comparison; source-change; target-change)
```
