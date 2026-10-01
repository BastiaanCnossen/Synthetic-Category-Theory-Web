# One-sided descriptions of directed pullbacks

Pasting the defining square with the product projection square gives
the one-sided pullbacks used in
`lem:Characterization_Left_And_Right_Fibrations`.
The matching in each square is the specified pasted matching, transported
through the endpoint projection comparison. No matching is discarded.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module FirstFactor; module SecondFactor)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullbackCone-isPullback; pullback-restrict-equivalence; pullback-comparison)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)

module Source {A B : CAT} (f : MAP A B) where
  module D = DirectedPullback f (id B) using (category)
  module Product = FirstFactor f B using (square; square-isPullback)
  product-square = coneSwap Product.square
  module Paste = Pasting endpoints (pr₁ {B} {B}) f product-square
    (pullback-swap Product.square Product.square-isPullback)
    using (module Paste; paste-isPullback)
  original = pullbackCone endpoints (productMap f (id B))
  pasted = Paste.Paste.flatten original

  square : Cone (ev₀ {B}) f D.category
  square = changeLeft (pair-β₁ ev₀ ev₁) pasted

  square-isPullback : IsPullback square
  square-isPullback = ChangeLeft.preserve (pair-β₁ ev₀ ev₁) f pasted
    (Paste.paste-isPullback original (pullbackCone-isPullback endpoints (productMap f (id B))))

module Target {A B : CAT} (f : MAP A B) where
  module D = DirectedPullback (id B) f using (category)
  module Product = SecondFactor B f using (square; square-isPullback)
  product-square = coneSwap Product.square
  module Paste = Pasting endpoints (pr₂ {B} {B}) f product-square
    (pullback-swap Product.square Product.square-isPullback)
    using (module Paste; paste-isPullback)
  original = pullbackCone endpoints (productMap (id B) f)
  pasted = Paste.Paste.flatten original

  square : Cone (ev₁ {B}) f D.category
  square = changeLeft (pair-β₂ ev₀ ev₁) pasted

  square-isPullback : IsPullback square
  square-isPullback = ChangeLeft.preserve (pair-β₂ ev₀ ev₁) f pasted
    (Paste.paste-isPullback original (pullbackCone-isPullback endpoints (productMap (id B) f)))

module EvaluationSquares {A B : CAT} (f : MAP A B) where
  open Evaluation f

  source-square = conePre directed-ev₀ (Source.square f)
  target-square = conePre directed-ev₁ (Target.square f)

  left-to-pullback : IsEquiv directed-ev₀ → IsPullback source-square
  left-to-pullback = pullback-restrict-equivalence (Source.square f) directed-ev₀
    (Source.square-isPullback f)

  pullback-to-left : IsPullback source-square → IsEquiv directed-ev₀
  pullback-to-left e = pullback-comparison source-square (Source.square f)
    directed-ev₀ (coneIso-id source-square) e (Source.square-isPullback f)

  right-to-pullback : IsEquiv directed-ev₁ → IsPullback target-square
  right-to-pullback = pullback-restrict-equivalence (Target.square f) directed-ev₁
    (Target.square-isPullback f)

  pullback-to-right : IsPullback target-square → IsEquiv directed-ev₁
  pullback-to-right e = pullback-comparison target-square (Target.square f)
    directed-ev₁ (coneIso-id target-square) e (Target.square-isPullback f)
```

The final four declarations give the criterion for the displayed restricted
squares. `EndpointNormalization` identifies their matching with endpoint
evaluation; `Section02.PullbackCriterion` proves the criterion for the
square defined directly by `evaluate-post`.
