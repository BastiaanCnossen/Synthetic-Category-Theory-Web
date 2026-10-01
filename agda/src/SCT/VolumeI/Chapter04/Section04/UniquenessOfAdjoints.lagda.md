# Uniqueness of right adjoints

For `prop:Uniqueness_Of_Adjoints` and its associated exercise, compare
the universal counits of the two adjunctions at the identity parameter.
Their comparison expressions are inverse. Rezk recognition therefore
identifies the two right adjoint functors. This proof does not use
functoriality of universals or the converse hom-adjunction criterion.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.UniquenessOfAdjoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.AdjunctionCounits 𝒯 M ℱ P I E S Q public
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionCalculusLifts as InverseLifts
open import SCT.VolumeI.Chapter02.Section03.RezkIdentification 𝒯 M ℱ P I E R using (module Identify)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UniversalCounits as Universal

module RightAdjoints {C D : CAT} {l : MAP C D} {r r′ : MAP D C}
  (a : Adjunction l r) (b : Adjunction l r′) where
  private
    module CounitComparison = Universal.At.Compare 𝒯 M ℱ P I E S Q D
      (adjunction-counit a (id D)) (adjunction-counit b (id D))
      using (forward; backward; backward-forward; forward-backward)

  identification : r =₁ r′
  identification = comp-unitʳ r′ ∙
    (Identify.identification CounitComparison.forward
      (InverseLifts.At.lift 𝒯 M ℱ P I E S Q D CounitComparison.forward CounitComparison.backward
        CounitComparison.forward-backward CounitComparison.backward-forward) ∙ (comp-unitʳ r) ⁻¹)
```
