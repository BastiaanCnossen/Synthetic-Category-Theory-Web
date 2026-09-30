# The evaluated pullback comparison

The comparison of relative functor categories gives an equivalence on
mapping animae. Its evaluation is identified with the entire mapped
cone, including the matching. This isolates the remaining comparison
with evaluation by the proposed dependent-product evaluation map.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackCones 𝒯 M ℱ P using (module PullbackComparison)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackConeFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeEvaluation 𝒯 M ℱ P using () renaming (module Evaluation to ConeEvaluation)

module FamiliesComparison {S T C D E K : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) (k : MAP K T) where
  module Candidate = Evaluation p ΠC ΠD ΠE u v using (module Q; module R)
  module Compared = PullbackComparison p ΠC ΠD ΠE u v k
    using (k′; mapped; forward; forward-cone; forward-isEquiv)
  module Evaluated = ConeEvaluation Compared.k′ u v using (value)
  module Family = Families.At Compared.k′ u v Compared.forward using (target; module Compared)
  abstract
    evaluated-cone : ConeIso Family.target (Evaluated.value Compared.mapped)
    evaluated-cone = Family.Compared.evaluated-comparison Compared.mapped Compared.forward-cone
  maps : MAP (MapOver k Candidate.Q.projection) (MapOver Compared.k′ Candidate.R.projection)
  maps = mapPost Compared.forward
  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv Compared.forward Compared.forward-isEquiv
```
