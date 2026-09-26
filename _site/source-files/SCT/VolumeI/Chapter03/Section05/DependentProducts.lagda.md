# Dependent products and relative currying

This is `def:Dependent_Product`. Its universal property concerns the
specified composite of base change and postcomposition by evaluation.
It does not postulate an unrelated equivalence of the two mapping
animae. The inverse of that composite is relative currying.

The relative functor theory is developed in `Chapter03.RelativeCategories`.
This module adds the dependent-product universal property to that shared
language. Supporting calculations are grouped by currying, base change,
and internal functor categories.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.DependentProducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

module EvaluationAlong {S T C D : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D T)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) where

  uncurrying : {E : CAT} (t : MAP E T) → MAP (MapOver t g) (MapOver (pullback₂ {f = t} {p}) f)
  uncurrying t = Postcompose.maps (pullback₂ {f = t} {p}) ε ∘ BaseChange.maps p t g
record IsDependentProduct {S T C D : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D T)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) : Set (c ⊔ m) where
  field
    universal : {E : CAT} (t : MAP E T) → IsEquiv (EvaluationAlong.uncurrying p f g ε t)

record DependentProduct {S T C : CAT} (p : MAP S T) (f : MAP C S) : Set (c ⊔ m) where
  field
    category : CAT
    projection : MAP category T
    evaluation : FunctorOver (pullback₂ {f = projection} {p}) f
    isDependentProduct : IsDependentProduct p f projection evaluation

module RelativeCurrying {S T C : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) where
  open DependentProduct Π

  module At {E : CAT} (t : MAP E T) where
    source = MapOver t projection
    target = MapOver (pullback₂ {f = t} {p}) f

    uncurry : MAP source target
    uncurry = EvaluationAlong.uncurrying p f projection evaluation t

    uncurry-isEquiv : IsEquiv uncurry
    uncurry-isEquiv = IsDependentProduct.universal isDependentProduct t

    curry : MAP target source
    curry = IsEquiv.inverse uncurry-isEquiv

    curry-uncurry : (curry ∘ uncurry) =₁ id source
    curry-uncurry = (IsEquiv.sectionIso uncurry-isEquiv) ⁻¹

    uncurry-curry : (uncurry ∘ curry) =₁ id target
    uncurry-curry = (IsEquiv.retractionIso uncurry-isEquiv) ⁻¹

    factor : {X : CAT} (v : MAP X target) → FunctorLift uncurry v
    factor v = equiv-lift uncurry-isEquiv v

    reflect : {X : CAT} (u v : MAP X source) → (uncurry ∘ u) =₁ (uncurry ∘ v) → u =₁ v
    reflect = equiv-reflect uncurry-isEquiv
```

The two inverse comparisons apply to entire anima-parametrized families.
They are the equalities used in relative currying, not only existence
statements for individual functors.
