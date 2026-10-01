# Ordinary slices as directed pullbacks

This proves the directed-pullback assertion in the remark preceding
`lem:Functors_Into_Slice_Category`, together with its coslice dual.
The equivalences retain the one-sided cone matching and commute with
the forgetful projection to the ambient category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks as Directed

module SCT.VolumeI.Chapter04.Section03.SlicesAsDirectedPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter04.Section01.DirectedPullbacks 𝒯 M ℱ P I
  using (module DirectedPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (ConeIso; conePre; module UniversalCone; pullback-comparison)

module SliceComparison {C : CAT} (x : Obj-abs C) where
  module S = EndpointFiber (id C) (const x)
  module D = DirectedPullback (id C) x
  module Ordinary = SliceEndpoint x using (square; square-isPullback)
  module Target = Directed.Target 𝒯 M ℱ P I x using (square; square-isPullback)
  module U = UniversalCone Target.square Target.square-isPullback using (factor; factor-β)

  forward : MAP (Slice C x) D.category
  forward = U.factor Ordinary.square
  comparison : ConeIso (conePre forward Target.square) Ordinary.square
  comparison = U.factor-β Ordinary.square
  forward-isEquiv : IsEquiv forward
  forward-isEquiv = pullback-comparison Ordinary.square Target.square forward comparison
    Ordinary.square-isPullback Target.square-isPullback

  arrow-comparison : (D.diagram ∘ forward) =₁ S.arrow
  arrow-comparison = ConeIso.leftIso comparison
  projection-comparison : (D.left ∘ forward) =₁ (slice-projection x)
  projection-comparison = comp-unitˡ S.base ∙
    (S.source-frame ∙
      ((ev₀ ◁ arrow-comparison) ∙
        (comp-assoc forward D.diagram ev₀ ∙
          ((D.source-frame ⁻¹ ▷ forward) ∙ (comp-unitˡ D.left ⁻¹ ▷ forward)))))

module CosliceComparison {C : CAT} (x : Obj-abs C) where
  module S = EndpointFiber (const x) (id C)
  module D = DirectedPullback x (id C)
  module Ordinary = CosliceEndpoint x using (square; square-isPullback)
  module Target = Directed.Source 𝒯 M ℱ P I x using (square; square-isPullback)
  module U = UniversalCone Target.square Target.square-isPullback using (factor; factor-β)

  forward : MAP (Coslice C x) D.category
  forward = U.factor Ordinary.square
  comparison : ConeIso (conePre forward Target.square) Ordinary.square
  comparison = U.factor-β Ordinary.square
  forward-isEquiv : IsEquiv forward
  forward-isEquiv = pullback-comparison Ordinary.square Target.square forward comparison
    Ordinary.square-isPullback Target.square-isPullback

  arrow-comparison : (D.diagram ∘ forward) =₁ S.arrow
  arrow-comparison = ConeIso.leftIso comparison
  projection-comparison : (D.right ∘ forward) =₁ (coslice-projection x)
  projection-comparison = comp-unitˡ S.base ∙
    (S.target-frame ∙
      ((ev₁ ◁ arrow-comparison) ∙
        (comp-assoc forward D.diagram ev₁ ∙
          ((D.target-frame ⁻¹ ▷ forward) ∙ (comp-unitˡ D.right ⁻¹ ▷ forward)))))
```
