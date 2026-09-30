# The matching needed for the direct comparison

Postcompose a test family with the manuscript's comparison and then use
the equivalence obtained from the two relative pullback squares. Each
projection agrees with uncurrying for the dependent product of the
original pullback. The calculations below construct these two agreements.

Their compatibility with the specified matching remains an input named
`Matching`. Given it, reflection through the relative pullback identifies
the composite with uncurrying. Relative postcomposition then detects the
desired equivalence. Only the source and target tests are needed.

This is a conditional criterion for the manuscript's direct comparison.
It does not assert the missing matching or the preservation theorem.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentProductPullbackCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (module UniversalCone)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentProductPullbackComparison 𝒯 M ℱ P using (module Direct)
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackCones 𝒯 M ℱ P using (module PullbackComparison)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying 𝒯 M ℱ P using (module Uncurrying)
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingNaturality 𝒯 M ℱ P using (module Natural)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionLaws 𝒯 M ℱ P
  using (postcompose-composite; postcompose-identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionDetection 𝒯 M ℱ P using (detect)

module Criterion {S T C D E : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) where
  module Diagram = Direct p ΠC ΠD ΠE u v using (iu; iv; module Q; module R; module WithProduct)

  module WithProduct (ΠR : DependentProduct p Diagram.R.projection) where
    module Chosen = Diagram.WithProduct ΠR using (over; functor; first; second; first-comparison; second-comparison)

    module At {K : CAT} (k : MAP K T) where
      module Tested = PullbackComparison p ΠC ΠD ΠE u v k
        using (forward; forward-cone; forward-isEquiv; target; target-isPullback; k′;
          module UC; module UD; module TargetU; module TargetV)
      module Post = Postcompose k Chosen.over using (functor; maps; maps-as-core)
      module Evaluated = Uncurrying p Diagram.R.projection ΠR k using (functor; functor-isEquiv)
      module First = Postcompose k Diagram.Q.first using (functor)
      module Second = Postcompose k Diagram.Q.second using (functor)
      H = Tested.forward
      F = Post.functor
      U = Evaluated.functor
      source = conePre (H ∘ F) Tested.target
      target = conePre U Tested.target
      first = Cone.left Tested.target
      second = Cone.right Tested.target

      opaque
        first-comparison : Cone.left source =₁ Cone.left target
        first-comparison = Natural.comparison p Diagram.R.projection f ΠR ΠC Diagram.R.first k ∙
          ((Tested.UC.functor ◁
            (postcompose-identification k Chosen.first-comparison ∙
              postcompose-composite k Chosen.over Diagram.Q.first)) ∙
          (comp-assoc F First.functor Tested.UC.functor ∙
          ((ConeIso.leftIso Tested.forward-cone ▷ F) ∙ (comp-assoc F H first) ⁻¹)))

        second-comparison : Cone.right source =₁ Cone.right target
        second-comparison = Natural.comparison p Diagram.R.projection g ΠR ΠD Diagram.R.second k ∙
          ((Tested.UD.functor ◁
            (postcompose-identification k Chosen.second-comparison ∙
              postcompose-composite k Chosen.over Diagram.Q.second)) ∙
          (comp-assoc F Second.functor Tested.UD.functor ∙
          ((ConeIso.rightIso Tested.forward-cone ▷ F) ∙ (comp-assoc F H second) ⁻¹)))

      Matching : Set m
      Matching = (Cone.match target ∙ (Tested.TargetU.functor ◁ first-comparison)) =₂
        ((Tested.TargetV.functor ◁ second-comparison) ∙ Cone.match source)

      module Verified (matching : Matching) where
        module Reflected = UniversalCone Tested.target Tested.target-isPullback using (reflect)

        opaque
          comparison : (H ∘ F) =₁ U
          comparison = Reflected.reflect (H ∘ F) U
            (record { leftIso = first-comparison ; rightIso = second-comparison ; compatible = matching })

          functor-isEquiv : IsEquiv Post.functor
          functor-isEquiv = equiv-cancel-left F H Tested.forward-isEquiv
            (equiv-transport (comparison ⁻¹) Evaluated.functor-isEquiv)

          maps-isEquiv : IsEquiv Post.maps
          maps-isEquiv = equiv-transport (Post.maps-as-core ⁻¹)
            (mapPost-isEquiv Post.functor functor-isEquiv)

    verified : ({K : CAT} (k : MAP K T) → At.Matching k) → IsEquiv Chosen.functor
    verified matching = detect Chosen.over
      (λ k → At.Verified.maps-isEquiv k (matching k))
```
