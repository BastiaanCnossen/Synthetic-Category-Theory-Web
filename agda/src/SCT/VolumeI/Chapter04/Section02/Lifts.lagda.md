# Left and right fibrations and their lifting categories

`IsLeftFibration` and `IsRightFibration` are exactly
`def:Left_And_Right_Fibrations`. The pullbacks below implement
`def:Category_Of_Lifts`, including arbitrary absolute parameter categories.
The equivalence of the structural functor is the assertion of
`cor:Left_Fibrations_Have_Unique_Lifts`. Its converse tests the universal
parameter, rather than assuming detection on absolute objects.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.Lifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalBaseChangeEquivalences 𝒯 P
  using (equivalence-all-base-changes; all-base-changes-equivalence)

module Fibration {A B : CAT} (f : MAP A B) where
  open Evaluation f public

  IsLeftFibration IsRightFibration : Set m
  IsLeftFibration = IsEquiv directed-ev₀
  IsRightFibration = IsEquiv directed-ev₁

  module CovariantLifts {Γ : CAT} (q : MAP Γ Left.category) where
    category : CAT
    category = Pullback directed-ev₀ q

    diagram : MAP category (Ar A)
    diagram = pullback₁

    parameter : MAP category Γ
    parameter = pullback₂

    matching : (directed-ev₀ ∘ diagram) =₁ (q ∘ parameter)
    matching = pullbackMatch

    unique-lifts : IsLeftFibration → IsEquiv parameter
    unique-lifts e = equivalence-all-base-changes e q

  module ContravariantLifts {Γ : CAT} (q : MAP Γ Right.category) where
    category : CAT
    category = Pullback directed-ev₁ q

    diagram : MAP category (Ar A)
    diagram = pullback₁

    parameter : MAP category Γ
    parameter = pullback₂

    matching : (directed-ev₁ ∘ diagram) =₁ (q ∘ parameter)
    matching = pullbackMatch

    unique-lifts : IsRightFibration → IsEquiv parameter
    unique-lifts e = equivalence-all-base-changes e q

  unique-covariant-lifts-left-fibration :
    ({Γ : CAT} (q : MAP Γ Left.category) → IsEquiv (CovariantLifts.parameter q)) →
    IsLeftFibration
  unique-covariant-lifts-left-fibration = all-base-changes-equivalence

  unique-contravariant-lifts-right-fibration :
    ({Γ : CAT} (q : MAP Γ Right.category) → IsEquiv (ContravariantLifts.parameter q)) →
    IsRightFibration
  unique-contravariant-lifts-right-fibration = all-base-changes-equivalence
```
