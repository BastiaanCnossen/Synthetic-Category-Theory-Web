# Relative internal functor categories along exponentiable functors

For `def:Relative_Functor_Category`, exponentiability supplies the dependent
product of `D ×_S C → C` along `C → S`. The evaluation is its evaluation
followed by projection to `D`.

The theorem below uses the literal map specified in the manuscript:
base-change a functor over `S`, then postcompose with evaluation. Its
inverse supplies relative currying. Both inverse identifications take
place in the relative mapping anima, and thus retain the base triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctors
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.RelativeInternalFunctors 𝒯 M ℱ P using (module Internal)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.InternalEvaluation 𝒯 M ℱ P using (module Evaluation)

module FunctorCategory {C D S : CAT} (p : MAP C S) (q : MAP D S) (ep : IsExponentiable p) where
  product = Exponentiable.dependent-product ep (pullback₂ {f = q} {p})
  open Internal p q product public using (category; projection; structure; evaluation; evaluation-triangle)

  module At {E : CAT} (t : MAP E S) where
    open Internal.At p q product t public using (source-structure)
    open Evaluation.At p q product t public using (uncurrying; uncurrying-isEquiv)

    curry : MAP (MapOver source-structure q) (MapOver t projection)
    curry = IsEquiv.inverse uncurrying-isEquiv

    abstract
      curry-uncurry : (curry ∘ uncurrying) =₁ id (MapOver t projection)
      curry-uncurry = (IsEquiv.sectionIso uncurrying-isEquiv) ⁻¹

      uncurry-curry : (uncurrying ∘ curry) =₁ id (MapOver source-structure q)
      uncurry-curry = (IsEquiv.retractionIso uncurrying-isEquiv) ⁻¹
```
