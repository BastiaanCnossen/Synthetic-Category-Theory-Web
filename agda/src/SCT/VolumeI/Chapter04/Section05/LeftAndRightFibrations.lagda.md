# Left and right fibrations are cocartesian and cartesian

The directed evaluation of a left or right fibration is an equivalence.
Its chosen inverse therefore supplies the required adjoint section. In
particular every equivalence is both cartesian and cocartesian. These are
the first two items of `lem:Projection_Is_Cocartesian_Fibration`; the
terminal and product-projection examples are separate assertions.

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

module SCT.VolumeI.Chapter04.Section05.LeftAndRightFibrations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section04.EquivalenceAdjunctions 𝒯 M ℱ P I E S
  using (equivalence-left-adjoint-section; equivalence-right-adjoint-section)
open import SCT.VolumeI.Chapter04.Section02.Equivalences 𝒯 M ℱ P I
  using (equivalence-isLeftFibration; equivalence-isRightFibration)

left-isCocartesian : {A B : CAT} (f : MAP A B) →
  IsEquiv (Evaluation.directed-ev₀ f) → Fibration.CocartesianFibration f
left-isCocartesian f ef = record
  { lift = IsEquiv.inverse ef
  ; left-adjoint-section = equivalence-left-adjoint-section (Evaluation.directed-ev₀ f) ef }

right-isCartesian : {A B : CAT} (f : MAP A B) →
  IsEquiv (Evaluation.directed-ev₁ f) → Fibration.CartesianFibration f
right-isCartesian f ef = record
  { lift = IsEquiv.inverse ef
  ; right-adjoint-section = equivalence-right-adjoint-section (Evaluation.directed-ev₁ f) ef }

equivalence-isCocartesian : {A B : CAT} (f : MAP A B) →
  IsEquiv f → Fibration.CocartesianFibration f
equivalence-isCocartesian f ef = left-isCocartesian f (equivalence-isLeftFibration f ef)

equivalence-isCartesian : {A B : CAT} (f : MAP A B) →
  IsEquiv f → Fibration.CartesianFibration f
equivalence-isCartesian f ef = right-isCartesian f (equivalence-isRightFibration f ef)
```
