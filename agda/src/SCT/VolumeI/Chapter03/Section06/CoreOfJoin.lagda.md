# The core of a join

For `prop:core_of_join`, take cores of the specified boundary pullback.
The core of the weakened boundary inclusion is an equivalence, so the
same holds for the core of the join inclusion. Combining this with the
coproduct comparison gives the canonical equivalence on cores.

This proof also works for the absolute relative join over any base.
It uses the dependent-product axiom's boundary pullback clause, not
contextual coproducts or the pushout clause over that base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter02.Section01.IntervalCore as IntervalCore
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.CoreOfJoin
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (K : IntervalCore.IntervalCoreAxiom 𝒯 M B I)
  (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P using (mappedCone; map-preserves-pullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback-converse)
open import SCT.VolumeI.Chapter02.Section01.CoreCoproducts 𝒯 M B P U I K using (coreCopair; coreCopair-isEquiv)
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.BoundaryCore 𝒯 M B P U I K using (weakened-boundary-core-isEquiv)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J

module RelativeCore {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) where
  module Boundary = BoundaryComparison dataJoin p q

  abstract
    inclusion-core-isEquiv : IsEquiv (mapPost {C = One} (inclusion p q))
    inclusion-core-isEquiv = degenerate-pullback-converse (weakened-boundary-core-isEquiv Γ)
      (mappedCone One Boundary.cone) (map-preserves-pullback One Boundary.cone (boundary-isEquiv p q))

  comparison : MAP (Core C ⊔ Core D) (Core (JoinOver p q))
  comparison = copair (mapPost (inclusion p q ∘ in₁)) (mapPost (inclusion p q ∘ in₂))

  abstract
    comparison-factorization : (mapPost (inclusion p q) ∘ coreCopair C D) =₁ comparison
    comparison-factorization = copair-cong (mapPost-comp in₁ (inclusion p q)) (mapPost-comp in₂ (inclusion p q)) ∙
      copair-post (mapPost in₁) (mapPost in₂) (mapPost (inclusion p q))

    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = equiv-transport comparison-factorization
      (equiv-compose (coreCopair C D) (mapPost (inclusion p q)) (coreCopair-isEquiv C D) inclusion-core-isEquiv)
```
