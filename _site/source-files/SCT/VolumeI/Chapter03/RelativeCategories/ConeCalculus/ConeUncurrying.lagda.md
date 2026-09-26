# Uncurrying relative cone comparisons

The second leg of a relative cone is a named structure functor. Its
uncurried matching is normalized to `f ∘ pr₂`. Naturality of the chosen
normalization makes a cone comparison into a native triangle comparison.

The final theorem gives the local triangle beta rule for relative
currying. Comparison with substitution into the universal evaluation is
a separate restriction calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingCompatibility 𝒯 M ℱ using (funPost-uncurry-natural)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameNaturality 𝒯 M ℱ P using (constant-name-natural)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

evalMatch : {X C D S : CAT} {f : MAP C S} {g : MAP D S} →
  (s : Cone (funPost g) (nameFun f) X) →
  (g ∘ funUncurry (Cone.left s)) =₁ (f ∘ pr₂)
evalMatch {f = f} {g} s = uncurry-constant-name f (Cone.right s) ∙
  (funUncurryIso (Cone.match s) ∙ (funPost-uncurry g (Cone.left s)) ⁻¹)

relative-cone-comparison : {X C D S : CAT} {f : MAP C S} {g : MAP D S}
  {s t : Cone (funPost g) (nameFun f) X} (Φ : ConeIso s t) →
  (evalMatch t ∙ (g ◁ funUncurryIso (ConeIso.leftIso Φ))) =₂ evalMatch s
relative-cone-comparison {f = f} {g} {s} {t} Φ = isoComp-unitˡ-at (evalMatch s) ∙
  paste-iso-squares (τs ∙ fs ⁻¹) (τt ∙ ft ⁻¹) κs κt first third last
    (paste-iso-squares (fs ⁻¹) (ft ⁻¹) τs τt first second third
      (move-square ft second first fs (funPost-uncurry-natural g α)) rawSquare)
    ((isoComp-unitˡ-at κs) ⁻¹ ∙ constant-name-natural f β)
  where
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ
  fs = funPost-uncurry g (Cone.left s)
  ft = funPost-uncurry g (Cone.left t)
  κs = uncurry-constant-name f (Cone.right s)
  κt = uncurry-constant-name f (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)
  first = g ◁ funUncurryIso α
  second = funUncurryIso (funPost g ◁ α)
  third = funUncurryIso (nameFun f ◁ β)
  last = idIso (f ∘ pr₂)
  rawSquare = funUncurryIso-comp (nameFun f ◁ β) (Cone.match s) ∙
    ((funUncurry-isoMap _ _ ◁ ConeIso.compatible Φ) ∙
      (funUncurryIso-comp (Cone.match t) (funPost g ◁ α)) ⁻¹)

module CurriedTriangle {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (v : MAP (X × C) D) (over : (g ∘ v) =₁ (f ∘ pr₂)) where
  module Curried = Curry f g v over
  restricted = conePre Curried.functor (pullbackCone (funPost g) (nameFun f))
  leg = funUncurryIso (ConeIso.leftIso Curried.comparison)

  evaluation-with-image : funUncurry (Cone.left restricted) =₁ v
  evaluation-with-image = funCurry-β v ∙ leg

  native-beta : (over ∙ (g ◁ evaluation-with-image)) =₂ evalMatch restricted
  native-beta = relative-cone-comparison Curried.comparison ∙
    (isoComp-cong ((Curried.matching-comparison) ⁻¹) (idIso (g ◁ leg)) ∙
      ((isoComp-assoc-at over (g ◁ funCurry-β v) (g ◁ leg)) ⁻¹ ∙
        isoComp-cong (idIso over) (postWhisker-isoComp-at g (funCurry-β v) leg)))
```
