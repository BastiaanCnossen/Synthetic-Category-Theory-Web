# Naturality of the constant-name comparison

The normalized right leg of a relative cone is `f ∘ pr₂`. The chosen
comparison with that leg is natural in a map to the terminal category.
This supplies the right-leg calculation for a relative version of cone
uncurrying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyProductFunctor as FP
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FamilyNaturality as FN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyPairing as Pairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Param

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluationNaturality 𝒯 M
  using (post-evaluation-family; pre-identity-family; post-identity-family; constant-family-square)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open FP vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily; paste-family-squares)
open FN vocabulary terminal products productLaws composition vertical whiskering
  using (family-interchange-fixedOuter)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pairing-triangle₂)
open Param vocabulary terminal products productLaws composition vertical
  using (const-cong; unitˡ)

module Family {A X C S : CAT} (f : MAP C S)
  {u v : MAP X One} (γ : MAP A (u ＝ v)) where
  r : MAP X One → MAP (X × C) (One × C)
  r s = productMap s (id C)
  action = productFamily γ (const (idIso (id C)))
  initial = uncurryFamily (nameFun f ◁ γ)
  middle = funUncurry (nameFun f) ◁ action
  later = (f ∘ pr₂) ◁ action
  final : MAP A ((f ∘ pr₂ {C = X} {D = C}) ＝ (f ∘ pr₂))
  final = const {P = A} (idIso (f ∘ pr₂))

  α : (s : MAP X One) → funUncurry (nameFun f ∘ s) =₁ (funUncurry (nameFun f) ∘ r s)
  α s = funUncurry-restrict (nameFun f) s
  β : (s : MAP X One) → (funUncurry (nameFun f) ∘ r s) =₁ ((f ∘ pr₂) ∘ r s)
  β s = funCurry-β (f ∘ pr₂) ▷ r s
  η : (s : MAP X One) → (pr₂ ∘ r s) =₁ pr₂
  η s = comp-unitˡ pr₂ ∙ pair-β₂ (s ∘ pr₁) (id C ∘ pr₂)
  δ : (s : MAP X One) → ((f ∘ pr₂) ∘ r s) =₁ (f ∘ pr₂)
  δ s = (f ◁ η s) ∙ comp-assoc (r s) pr₂ f

  first : (const (α v) ∙ initial) =₁ (middle ∙ const (α u))
  first = uncurry-restrict-substitution (nameFun f) γ
  second : (const (β v) ∙ middle) =₁ (later ∙ const (β u))
  second = family-interchange-fixedOuter (funCurry-β (f ∘ pr₂)) action

  projection-natural : (const (η v) ∙ (pr₂ ◁ action)) =₁
    (const (idIso pr₂) ∙ const (η u))
  projection-natural = paste-family-squares
    (pair-β₂ (u ∘ pr₁) (id C ∘ pr₂)) (pair-β₂ (v ∘ pr₁) (id C ∘ pr₂))
    (comp-unitˡ pr₂) (comp-unitˡ pr₂) (pr₂ ◁ action)
    (const (idIso (id C ∘ pr₂))) (const (idIso pr₂))
    (isoComp-cong (pre-identity-family (id C) pr₂) (idIso _) ∙
      pairing-triangle₂ (γ ▷ pr₁) (const (idIso (id C)) ▷ pr₂))
    (constant-family-square (comp-unitˡ pr₂))

  third : (const (δ v) ∙ later) =₁ (final ∙ const (δ u))
  third = isoComp-cong (post-identity-family f pr₂) (idIso _) ∙
    post-evaluation-family f pr₂ action (η u) (η v) (const (idIso pr₂)) projection-natural

  grouped : (s : MAP X One) → funUncurry (nameFun f ∘ s) =₁ (f ∘ pr₂)
  grouped s = δ s ∙ (β s ∙ α s)
  regroup : (s : MAP X One) → grouped s =₂ uncurry-constant-name f s
  regroup s = isoComp-assoc-at (f ◁ η s) (comp-assoc (r s) pr₂ f) (β s ∙ α s)

  pasted : (const (grouped v) ∙ initial) =₁ (final ∙ const (grouped u))
  pasted = paste-family-squares (β u ∙ α u) (β v ∙ α v) (δ u) (δ v)
    initial later final
    (paste-family-squares (α u) (α v) (β u) (β v) initial middle later first second) third

  natural : (const (uncurry-constant-name f v) ∙ initial) =₁ const (uncurry-constant-name f u)
  natural = const-cong (regroup u) ∙
    (unitˡ (const (grouped u)) ∙
      (pasted ∙ isoComp-cong ((const-cong (regroup v)) ⁻¹) (idIso initial)))

constant-name-natural : {X C S : CAT} (f : MAP C S)
  {u v : MAP X One} (β : u =₁ v) →
  (uncurry-constant-name f v ∙ funUncurryIso (nameFun f ◁ β)) =₂ uncurry-constant-name f u
constant-name-natural f {u} {v} β = const-One (uncurry-constant-name f u) ∙
  (Family.natural f β ∙
    (isoComp-cong (const-One (uncurry-constant-name f v))
      (uncurryFamily-absolute (nameFun f ◁ β))) ⁻¹)
```
