# Postcomposition in the varying coordinate

Applying a functor to the second coordinate preserves its pairing with
the identity in the first coordinate, with the specified product frames.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PairedCoordinatePostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-id)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E using (post-identity)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFunctoriality as Functoriality
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as Frames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdentityFrames

module At {X A B C : CAT} (F : MAP B C) {u v : MAP (X × A) B} (β : MorphismExpression u v) where
  W = productMap (id X) F
  original = pair-expression (identity-expression pr₁) β
  result = pair-expression (identity-expression pr₁) (post-expression F β)
  source-change = pair-cong (comp-unitˡ (pr₁ {X} {A})) (idIso (F ∘ u))
  target-change = pair-cong (comp-unitˡ (pr₁ {X} {A})) (idIso (F ∘ v))
  source-frame = source-change ∙ productMap-pair (id X) F pr₁ u
  target-frame = target-change ∙ productMap-pair (id X) F pr₁ v
  module Mapped = Functoriality.At 𝒯 M ℱ P I E S (id X) F (identity-expression pr₁) β
  module ProductFrames = Frames.At 𝒯 M ℱ I (post-expression (id X) (identity-expression pr₁)) (post-expression F β)
    (comp-unitˡ pr₁) (comp-unitˡ pr₁) (idIso (F ∘ u)) (idIso (F ∘ v))

  abstract
    first : ExpressionIso
      (retarget-expression (post-expression (id X) (identity-expression (pr₁ {X} {A})))
        (comp-unitˡ pr₁) (comp-unitˡ pr₁)) (identity-expression pr₁)
    first = expressionIso-compose (IdentityFrames.At.comparison 𝒯 M ℱ P I E (comp-unitˡ pr₁))
      (retarget-expressionIso (post-identity (id X) pr₁) (comp-unitˡ pr₁) (comp-unitˡ pr₁))

    value : ExpressionIso (retarget-expression (post-expression W original) source-frame target-frame) result
    value = expressionIso-compose (pair-expression-cong first (retarget-id (post-expression F β)))
      (expressionIso-compose ProductFrames.value
        (expressionIso-compose (retarget-expressionIso Mapped.value source-change target-change)
          (expressionIso-inverse (retarget-assoc (post-expression W original)
            (productMap-pair (id X) F pr₁ u) (productMap-pair (id X) F pr₁ v) source-change target-change))))
```
