# The composition functor between functor categories

Curry the evaluation formula `((F,u),b) ↦ F(u(b))`. Its named values
agree with ordinary composition. Fixing either input gives the existing
precomposition or postcomposition functor, with retained uncurried images.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.InternalComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect; funIsoReflect-β)

product-pair : {Γ A B C D : CAT} (f : MAP A C) (g : MAP B D) (h : MAP Γ A) (k : MAP Γ B) →
  (productMap f g ∘ pair h k) =₁ pair (f ∘ h) (g ∘ k)
product-pair f g h k = pair-cong
  ((f ◁ pair-β₁ h k) ∙ comp-assoc (pair h k) pr₁ f)
  ((g ◁ pair-β₂ h k) ∙ comp-assoc (pair h k) pr₂ g) ∙
  pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair h k)

named-application : {Γ C D : CAT} (f : MAP C D) (r : MAP Γ One) (h : MAP Γ C) →
  (funEval ∘ pair (nameFun f ∘ r) h) =₁ (f ∘ h)
named-application f r h = (f ◁ pair-β₂ r h) ∙
  comp-assoc (pair r h) pr₂ f ∙ (funCurry-β (f ∘ pr₂) ▷ pair r h) ∙
  (comp-assoc (pair r h) (productMap (nameFun f) (id _)) funEval) ⁻¹ ∙
  (funEval ◁ (pair-cong (idIso (nameFun f ∘ r)) (comp-unitˡ h) ∙
    product-pair (nameFun f) (id _) r h) ⁻¹)

named-uncurry : {Γ C D : CAT} (f : MAP C D) (r : MAP Γ One) →
  funUncurry (nameFun f ∘ r) =₁ (f ∘ pr₂)
named-uncurry {C = C} f r = (f ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (r ∘ pr₁) (id C ∘ pr₂))) ∙
  comp-assoc (productMap r (id C)) pr₂ f ∙
  (funCurry-β (f ∘ pr₂) ▷ productMap r (id C)) ∙ funUncurry-restrict (nameFun f) r

module At (B C D : CAT) where
  X = Fun C D
  Y = Fun B C
  parameter = X × Y
  inner : MAP (parameter × B) C
  inner = funEval ∘ pair (pr₂ ∘ pr₁) pr₂
  input : MAP (parameter × B) (X × C)
  input = pair (pr₁ ∘ pr₁) inner
  diagram : MAP (parameter × B) D
  diagram = funEval ∘ input
  composeFunctor : MAP parameter (Fun B D)
  composeFunctor = funCurry diagram

  module Apply {Γ : CAT} (F : MAP Γ X) (u : MAP Γ Y) where
    step : MAP (Γ × B) (parameter × B)
    step = productMap (pair F u) (id B)
    first : ((pr₁ ∘ pr₁) ∘ step) =₁ (F ∘ pr₁)
    first = (pair-β₁ F u ▷ pr₁) ∙ (comp-assoc pr₁ (pair F u) pr₁) ⁻¹ ∙
      (pr₁ ◁ pair-β₁ (pair F u ∘ pr₁) (id B ∘ pr₂)) ∙ comp-assoc step pr₁ pr₁
    second : ((pr₂ ∘ pr₁) ∘ step) =₁ (u ∘ pr₁)
    second = (pair-β₂ F u ▷ pr₁) ∙ (comp-assoc pr₁ (pair F u) pr₂) ⁻¹ ∙
      (pr₂ ◁ pair-β₁ (pair F u ∘ pr₁) (id B ∘ pr₂)) ∙ comp-assoc step pr₁ pr₂
    inner-comparison : (inner ∘ step) =₁ funUncurry u
    inner-comparison = (funEval ◁
      (pair-cong second (pair-β₂ (pair F u ∘ pr₁) (id B ∘ pr₂)) ∙
        pair-pre (pr₂ ∘ pr₁) pr₂ step)) ∙ comp-assoc step (pair (pr₂ ∘ pr₁) pr₂) funEval
    input-comparison : (input ∘ step) =₁ pair (F ∘ pr₁) (funUncurry u)
    input-comparison = pair-cong first inner-comparison ∙ pair-pre (pr₁ ∘ pr₁) inner step
    comparison : funUncurry (composeFunctor ∘ pair F u) =₁
      (funEval ∘ pair (F ∘ pr₁) (funUncurry u))
    comparison = (funEval ◁ input-comparison) ∙ comp-assoc step input funEval ∙
      (funCurry-β diagram ▷ step) ∙ funUncurry-restrict composeFunctor (pair F u)

  module Named (F : MAP C D) (u : MAP B C) where
    raw : funUncurry (composeFunctor ∘ pair (nameFun F) (nameFun u)) =₁ funUncurry (nameFun (F ∘ u))
    raw = (funCurry-β ((F ∘ u) ∘ pr₂)) ⁻¹ ∙ (comp-assoc pr₂ u F) ⁻¹ ∙
      named-application F pr₁ (u ∘ pr₂) ∙
      (funEval ◁ pair-cong (idIso (nameFun F ∘ pr₁)) (funCurry-β (u ∘ pr₂))) ∙
      Apply.comparison (nameFun F) (nameFun u)
    comparison : (composeFunctor ∘ pair (nameFun F) (nameFun u)) =₁ nameFun (F ∘ u)
    comparison = funIsoReflect _ _ raw
    image : funUncurryIso comparison =₂ raw
    image = funIsoReflect-β _ _ raw

  module FixRight (u : MAP B C) where
    insertion : MAP X parameter
    insertion = pair (id X) (const (nameFun u))
    raw : funUncurry (composeFunctor ∘ insertion) =₁ funUncurry (funPre {D = D} u)
    raw = (funPre-β u) ⁻¹ ∙
      (funEval ◁ pair-cong (idIso (id X ∘ pr₁)) (named-uncurry u (terminate X))) ∙
      Apply.comparison (id X) (const (nameFun u))
    comparison : (composeFunctor ∘ insertion) =₁ funPre u
    comparison = funIsoReflect _ _ raw
    image : funUncurryIso comparison =₂ raw
    image = funIsoReflect-β _ _ raw

  module FixLeft (F : MAP C D) where
    insertion : MAP Y parameter
    insertion = pair (const (nameFun F)) (id Y)
    raw : funUncurry (composeFunctor ∘ insertion) =₁ funUncurry (funPost {C = B} F)
    raw = (funPost-β F) ⁻¹ ∙ named-application F (terminate Y ∘ pr₁) funEval ∙
      (funEval ◁ pair-cong (comp-assoc pr₁ (terminate Y) (nameFun F)) (funUncurry-id B C)) ∙
      Apply.comparison (const (nameFun F)) (id Y)
    comparison : (composeFunctor ∘ insertion) =₁ funPost F
    comparison = funIsoReflect _ _ raw
    image : funUncurryIso comparison =₂ raw
    image = funIsoReflect-β _ _ raw
```
