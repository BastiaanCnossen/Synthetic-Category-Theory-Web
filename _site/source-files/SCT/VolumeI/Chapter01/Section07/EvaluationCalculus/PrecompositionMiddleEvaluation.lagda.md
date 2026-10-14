# Evaluating the common precomposition middle

The normalized product square identifies the chosen middle frame with the
route through the compositor of precomposition. Its computation rule and
the evaluated product square retain the same coherent matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionMiddleEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (preComp)
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionProductFrameComparison as Product
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedAssociativitySquare as Evaluated
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionComposition as Composition

module At {C D : CAT} (K : CAT) (l : MAP C D) (r : MAP D C) where
  X = Fun C K
  Y = Fun D K
  L : MAP X Y
  L = funPre {D = K} r
  R : MAP Y X
  R = funPre {D = K} l
  e : MAP (X × C) K
  e = funEval
  W : MAP (X × D) (X × C)
  W = productMap (id X) r
  Jl : MAP (X × C) (X × D)
  Jl = productMap (id X) l
  β : funUncurry L =₁ (e ∘ W)
  β = funPre-β r
  δrl = pair-cong (comp-unitˡ (pr₁ {X} {C})) (comp-assoc (pr₂ {X} {C}) l r)
  χlr = productRestriction-comp X l r
  χrl = productRestriction-comp X r l
  q : funUncurry (R ∘ L) =₁ (funUncurry L ∘ Jl)
  q = funPre-uncurry l L
  u : funUncurry (R ∘ L) =₁ (e ∘ pair pr₁ (r ∘ (l ∘ pr₂)))
  u = (e ◁ δrl) ∙ ((e ◁ χlr) ∙ (comp-assoc Jl W e ∙ ((β ▷ Jl) ∙ q)))
  module ProductFrame = Product.At 𝒯 M ℱ K l r u
  module F = ProductFrame.F
  module Image = Evaluated.At 𝒯 W Jl W e (δrl ∙ χlr) F.product-frame χrl ProductFrame.ψ β ProductFrame.value
  module Composite = Composition.CompositorEvaluation 𝒯 M ℱ P r l L
  tail = funPre-uncurry r (R ∘ L) ∙ funUncurryIso (comp-assoc L R L)

  abstract
    unit-normal : u =₂ (Image.dE ∙ q)
    unit-normal = (isoComp-assoc-at (e ◁ (δrl ∙ χlr)) (comp-assoc Jl W e ∙ (β ▷ Jl)) q) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ (δrl ∙ χlr))) ((isoComp-assoc-at (comp-assoc Jl W e) (β ▷ Jl) q) ⁻¹) ∙
      isoComp-cong ((postWhisker-isoComp-at e δrl χlr) ⁻¹)
        (idIso (comp-assoc Jl W e ∙ ((β ▷ Jl) ∙ q))) ∙
      (isoComp-assoc-at (e ◁ δrl) (e ◁ χlr) (comp-assoc Jl W e ∙ ((β ▷ Jl) ∙ q))) ⁻¹

    prefix : F.restricted-frame =₂
      (Image.nE ∙ ((funUncurry L ◁ χrl) ∙ (comp-assoc W Jl (funUncurry L) ∙ (q ▷ W))))
    prefix = Image.append q ∙ isoComp-cong (idIso F.evaluation-frame) (preWhisker W ◁ unit-normal)

    value : F.middle =₂
      (Image.nE ∙ (funPre-uncurry (l ∘ r) L ∙ funUncurryIso (preComp r l ▷ L)))
    value = isoComp-cong (idIso Image.nE) (Composite.comparison ⁻¹) ∙
      isoComp-cong (idIso Image.nE)
        (isoComp-cong (idIso (funUncurry L ◁ χrl)) (isoComp-assoc-at (comp-assoc W Jl (funUncurry L)) (q ▷ W) tail)) ∙
      isoComp-cong (idIso Image.nE)
        (isoComp-assoc-at (funUncurry L ◁ χrl) (comp-assoc W Jl (funUncurry L) ∙ (q ▷ W)) tail) ∙
      isoComp-assoc-at Image.nE ((funUncurry L ◁ χrl) ∙ (comp-assoc W Jl (funUncurry L) ∙ (q ▷ W))) tail ∙
      isoComp-cong prefix (idIso tail) ∙
      (isoComp-assoc-at F.evaluation-frame (u ▷ W) tail) ⁻¹
```
