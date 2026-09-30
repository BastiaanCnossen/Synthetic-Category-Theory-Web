# Uncurrying reflects framed identifications

Recovery after uncurrying and compatibility of currying with framed
identifications imply reflection. Thus an identification after evaluation
can be used to prove an identification of transformations, without
discarding either endpoint condition.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingUncurryingRecovery as Recovery
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressionComparisons as Comparisons

uncurry-reflect : {Γ X C : CAT} {f g : MAP Γ (Fun X C)}
  {α β : MorphismExpression f g} →
  ExpressionIso (uncurry-expression α) (uncurry-expression β) → ExpressionIso α β
uncurry-reflect {f = f} {g} {α} {β} ξ = expressionIso-compose
  (Recovery.At.value 𝒯 M ℱ P I E β)
  (expressionIso-compose (Comparisons.At.value 𝒯 M ℱ P I E f g ξ)
    (expressionIso-inverse (Recovery.At.value 𝒯 M ℱ P I E α)))
```
