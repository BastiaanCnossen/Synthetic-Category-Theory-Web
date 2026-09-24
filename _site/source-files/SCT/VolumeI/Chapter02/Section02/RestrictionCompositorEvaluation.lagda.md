# The retained image of a restriction compositor at an object

Evaluate the chosen `preComp` identification and cancel its retained beta
comparison. This gives the exact remaining product-and-evaluation path.
`RestrictionEndpointComposition` normalizes that path into two successive
`evaluate-pre` comparisons while retaining the vertex associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section02.RestrictionCompositorEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

private
  abstract
    close-naturality : {X Y : CAT} {a₀ a₁ b₀ b₁ c₀ d₀ : MAP X Y}
      (prefix : c₀ =₁ d₀) (beta : b₁ =₁ c₀)
      (before : a₀ =₁ b₀) (after : a₁ =₁ b₁)
      (input : a₀ =₁ a₁) (image : b₀ =₁ b₁) (result : b₀ =₁ c₀) →
      (after ∙ input) =₂ (image ∙ before) → (beta ∙ image) =₂ result →
      ((prefix ∙ (beta ∙ after)) ∙ input) =₂ (prefix ∙ (result ∙ before))
    close-naturality prefix beta before after input image result square computation =
      isoComp-cong (idIso prefix)
        (isoComp-cong computation (idIso before) ∙
        ((isoComp-assoc-at beta image before) ⁻¹ ∙
        (isoComp-cong (idIso beta) square ∙ isoComp-assoc-at beta after input))) ∙
        isoComp-assoc-at prefix (beta ∙ after) input

module AtObject {A B D C : CAT} (f : MAP A B) (g : MAP B D) (x : Obj-abs A) where
  X = Fun D C
  i = insert {X = X} x
  F = productMap (id X) f
  G = productMap (id X) g
  GF = productMap (id X) (g ∘ f)
  κ = preComp {E = C} f g
  beta = funPre-β {D = C} (g ∘ f)
  product-comparison = productMap-cong (comp-unitˡ (id X)) (idIso (g ∘ f)) ∙
    productMap-comp (id X) (id X) f g
  leading = (funEval ◁ product-comparison) ∙
    (comp-assoc F G funEval ∙
      ((funPre-β g ▷ F) ∙ funPre-uncurry f (funPre g)))
  insertion = pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) x (g ∘ f)) ⁻¹) ∙
    productMap-pair (id X) (g ∘ f) (id X) (const x)
  prefix = (funEval ◁ insertion) ∙ comp-assoc i GF funEval

  abstract
    retained-image : (beta ∙ funUncurryIso κ) =₂ leading
    retained-image = cancel-inverse beta leading ∙
      isoComp-cong (idIso beta) (preComp-β f g)

    restricted-image : ((beta ▷ i) ∙ (funUncurryIso κ ▷ i)) =₂ (leading ▷ i)
    restricted-image = (preWhisker i ◁ retained-image) ∙
      (preWhisker-isoComp-at beta (funUncurryIso κ) i) ⁻¹

    comparison : (evaluate-pre {C = C} (g ∘ f) x ∙ (evaluate x ◁ κ)) =₂
      (prefix ∙ ((leading ▷ i) ∙ evaluate-uncurry x (funPre f ∘ funPre g)))
    comparison = close-naturality prefix (beta ▷ i)
      (evaluate-uncurry x (funPre f ∘ funPre g)) (evaluate-uncurry x (funPre (g ∘ f)))
      (evaluate x ◁ κ) (funUncurryIso κ ▷ i) (leading ▷ i)
      (Evaluation.natural x κ) restricted-image ∙
      isoComp-cong
        ((isoComp-assoc-at (funEval ◁ insertion) (comp-assoc i GF funEval)
          ((beta ▷ i) ∙ evaluate-uncurry x (funPre (g ∘ f)))) ⁻¹)
        (idIso (evaluate x ◁ κ))
```
