# Uncurrying through an identified evaluation diagram

A functor into a functor category may be evaluated using any specified
identification of its uncurried diagram. The comparison below retains
both endpoint restrictions and the chosen identification.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingIdentifiedPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductExpressions 𝒯 M ℱ P I E S using (external-product)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingPostcomposition as Uncurrying
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphicPostcomposition as Identified

module At {Γ X A D : CAT} (L : MAP A (Fun X D)) (H : MAP (A × X) D)
  (β : funUncurry L =₁ H) {f g : MAP Γ A} (α : MorphismExpression f g) where
  module U = Uncurrying.At 𝒯 M ℱ P I E S L α
    using (comparison; paired)
  module Beta = Identified.At 𝒯 M ℱ P I E β U.paired
    using (value)

  abstract
    value : ExpressionIso (retarget-expression (uncurry-expression (post-expression L α))
        ((β ▷ productMap f (id X)) ∙ funUncurry-restrict L f)
        ((β ▷ productMap g (id X)) ∙ funUncurry-restrict L g))
      (post-expression H (external-product α (id X)))
    value = expressionIso-compose Beta.value
      (expressionIso-compose (retarget-expressionIso U.comparison
          (β ▷ productMap f (id X)) (β ▷ productMap g (id X)))
        (expressionIso-inverse (retarget-assoc (uncurry-expression (post-expression L α))
          (funUncurry-restrict L f) (funUncurry-restrict L g)
          (β ▷ productMap f (id X)) (β ▷ productMap g (id X)))))
```
