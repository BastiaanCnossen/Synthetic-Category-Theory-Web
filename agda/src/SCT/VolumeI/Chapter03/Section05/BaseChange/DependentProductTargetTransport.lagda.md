# Transporting dependent products along a target equivalence

Postcompose evaluation by an equivalence over the base. The resulting
uncurrying map is the original one followed by the induced equivalence
on relative mapping animae. This transports a supplied dependent product
while retaining its projection and the new evaluation triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.DependentProductTargetTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionLaws 𝒯 M ℱ P using (postcompose-maps-composite)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionEquivalences 𝒯 M ℱ P using (module Post)

module Transport {S T C D : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (u : FunctorOver f g) (equivalence : IsEquiv (FunctorLift.lift u)) (Π : DependentProduct p f) where
  X = DependentProduct.category Π
  r = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  evaluation = compose-over u ε

  module At {K : CAT} (k : MAP K T) where
    k′ : MAP (Pullback k p) S
    k′ = pullback₂
    module BC = BaseChange p k r
    old = EvaluationAlong.uncurrying p f r ε k
    new = EvaluationAlong.uncurrying p g r evaluation k
    post = Postcompose.maps k′ u

    abstract
      comparison : new =₁ (post ∘ old)
      comparison = comp-assoc BC.maps (Postcompose.maps k′ ε) post ∙
        ((postcompose-maps-composite k′ ε u) ⁻¹ ▷ BC.maps)

      isEquiv : IsEquiv new
      isEquiv = equiv-transport (comparison ⁻¹)
        (equiv-compose old post (IsDependentProduct.universal (DependentProduct.isDependentProduct Π) k)
          (Post.maps-isEquiv k′ u equivalence))

  abstract
    universal : IsDependentProduct p g r evaluation
    universal = record { universal = At.isEquiv }

  dependent-product : DependentProduct p g
  dependent-product = record
    { category = X ; projection = r ; evaluation = evaluation ; isDependentProduct = universal }
```
