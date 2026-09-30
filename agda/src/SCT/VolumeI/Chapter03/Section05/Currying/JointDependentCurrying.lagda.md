# Joint source naturality of dependent currying

Curry a family after composing it with a changed-base functor. This
agrees with first currying the family and then composing over the
original base. Both arguments vary together.

Lift the joint uncurrying comparison through its equivalence on
identification animae. The resulting comparison has a specified image
under uncurrying. This computation is needed when transporting a
specified matching; bare reflection would supply only a comparison.

This is a new choice on relative functor categories. Agreement with
the earlier native currying comparisons is not asserted here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.JointDependentCurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying 𝒯 M ℱ P
  using (module Uncurrying)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.JointComposition 𝒯 M ℱ P using (module Joint)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.Section05.Currying.JointRelativeUncurrying 𝒯 M ℱ P using (module Natural)

module Currying {K L C S T : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) (k : MAP K T) (l : MAP L T) where
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  l′ : MAP (Pullback l p) S
  l′ = pullback₂
  parameter = FunOver l′ f × FunOver k l
  module UK = Uncurrying p f Π k using (functor; inverse; right-inverse; functor-isEquiv)
  module UL = Uncurrying p f Π l using (functor; inverse; right-inverse)
  module Old = Joint k l g using (functor)
  module New = Joint k′ l′ f using (functor)
  module Change = BaseChange p k l using (functor)
  module Uncurry = Natural p f g ε k l using (evaluated; comparison)

  curried-parameter : MAP parameter (FunOver l g × FunOver k l)
  curried-parameter = pair (UL.inverse ∘ pr₁) pr₂
  evaluated-parameter : MAP parameter (FunOver l′ f × FunOver k′ l′)
  evaluated-parameter = pair pr₁ (Change.functor ∘ pr₂)
  evaluated : MAP parameter (FunOver k′ f)
  evaluated = New.functor ∘ evaluated-parameter
  source : MAP parameter (FunOver k g)
  source = Old.functor ∘ curried-parameter
  target : MAP parameter (FunOver k g)
  target = UK.inverse ∘ evaluated

  opaque
    parameter-comparison : (Uncurry.evaluated ∘ curried-parameter) =₁ evaluated-parameter
    parameter-comparison = pair-cong
      (comp-unitˡ pr₁ ∙ ((UL.right-inverse ▷ pr₁) ∙
        ((comp-assoc pr₁ UL.inverse UL.functor) ⁻¹ ∙
          ((UL.functor ◁ pair-β₁ (UL.inverse ∘ pr₁) pr₂) ∙
            comp-assoc curried-parameter pr₁ UL.functor))))
      ((Change.functor ◁ pair-β₂ (UL.inverse ∘ pr₁) pr₂) ∙
        comp-assoc curried-parameter pr₂ Change.functor) ∙
      pair-pre (UL.functor ∘ pr₁) (Change.functor ∘ pr₂) curried-parameter

    source-evaluation : (UK.functor ∘ source) =₁ evaluated
    source-evaluation = (New.functor ◁ parameter-comparison) ∙
      (comp-assoc curried-parameter Uncurry.evaluated New.functor ∙
        ((Uncurry.comparison ▷ curried-parameter) ∙
          (comp-assoc curried-parameter Old.functor UK.functor) ⁻¹))

    target-evaluation : (UK.functor ∘ target) =₁ evaluated
    target-evaluation = comp-unitˡ evaluated ∙
      ((UK.right-inverse ▷ evaluated) ∙ (comp-assoc evaluated UK.inverse UK.functor) ⁻¹)

    prescribed-image : (UK.functor ∘ source) =₁ (UK.functor ∘ target)
    prescribed-image = target-evaluation ⁻¹ ∙ source-evaluation

    chosen : FunctorLift (postWhisker UK.functor) prescribed-image
    chosen = postWhisker-lift UK.functor UK.functor-isEquiv prescribed-image

    comparison : source =₁ target
    comparison = FunctorLift.lift chosen

    computation : (UK.functor ◁ comparison) =₂ prescribed-image
    computation = FunctorLift.comparison chosen

  restriction : {Y : CAT} (σ : MAP Y parameter) → (source ∘ σ) =₁ (target ∘ σ)
  restriction σ = comparison ▷ σ

  naturality : {Y : CAT} {σ τ : MAP Y parameter} (α : σ =₁ τ) →
    (restriction τ ∙ (source ◁ α)) =₂ ((target ◁ α) ∙ restriction σ)
  naturality α = interchange-at comparison α
```
