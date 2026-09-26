# Disjoint coproducts

For `cor:Disjoint_Coproducts`, apply universality to the two maps
`id C` and `Zero → D`, then use the coproduct unit equivalence. All cones
with initial vertex have the required comparison by initiality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section06.DisjointCoproducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (I : Initial.InitialStructure 𝒯 M) (B : Coproducts.CoproductStructure 𝒯 M)
  (P : Laws.PullbackStructure 𝒯) (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Initial.Initiality 𝒯 M I
open Coproducts.CoproductStructure B
open Laws.PullbackStructure P
open Universality 𝒯 M B P
open CoproductUniversality U
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.CoproductEquivalences 𝒯 M I B
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)

disjointCone : (C D : CAT) → Cone (in₂ {C} {D}) in₁ Zero
disjointCone C D = record { left = initiate D ; right = initiate C ; match = initial-iso _ _ }

module Disjointness (C D : CAT) where

  H = coproductMap (id C) (initiate D)
  unit = coproduct-unitʳ C
  comparison : (in₁ ∘ unit) =₁ H
  comparison = copair-cong (idIso (in₁ ∘ id C)) (initial-iso _ _) ∙
    copair-post (id C) (initiate C) in₁

  cospan : CospanMap (in₂ {C} {D}) H in₂ in₁
  cospan = record
    { left = id D ; right = unit ; base = id (C ⊔ D)
    ; leftSquare = (comp-unitˡ in₂) ⁻¹ ∙ comp-unitʳ in₂
    ; rightSquare = (comp-unitˡ H) ⁻¹ ∙ comparison }
  module F = CospanMap cospan
  module E = CospanEquivalence cospan (id-isEquiv D) (coproduct-unitʳ-isEquiv C) (id-isEquiv (C ⊔ D))
    using (pullbackMap-isEquiv)

  isPullback : IsPullback (disjointCone C D)
  isPullback = equiv-transport (initial-iso _ _)
    (equiv-compose (pullbackLift (coproductSquare₂ (id C) (initiate D))) F.pullbackMap
      (inclusion₂-isPullback (id C) (initiate D)) E.pullbackMap-isEquiv)

disjoint-isPullback : (C D : CAT) → IsPullback (disjointCone C D)
disjoint-isPullback = Disjointness.isPullback
```
