# Disjoint coproducts

For `cor:Disjoint_Coproducts`, apply universality to the two maps
`id C` and `Zero → D`, then use the coproduct unit equivalence. All cones
with initial vertex have the required comparison by initiality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Initial as Initial
import SCT.VolumeI.Chapter01.Section04.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section05.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section05.DisjointCoproducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (I : Initial.InitialStructure 𝒯 M) (B : Coproducts.CoproductStructure 𝒯 M)
  (P : Laws.PullbackStructure 𝒯) (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Initial.Initiality 𝒯 M I
open Coproducts.CoproductStructure B
open Laws.PullbackStructure P
open Universality 𝒯 M B P
open CoproductUniversality U
open import SCT.VolumeI.Chapter01.Section04.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section04.CoproductEquivalences 𝒯 M I B
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section05.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section05.CospanEquivalences 𝒯 P using (module CospanEquivalence)

disjointCone : (C D : CAT) → Cone (in₂ {C} {D}) in₁ Zero
disjointCone C D = record { left = initiate D ; right = initiate C ; match = initial-iso _ _ }

module Disjointness (C D : CAT) where

  H = coproductMap (id C) (initiate D)
  unit = coproduct-unitʳ C
  comparison : NatIso (in₁ ∘ unit) H
  comparison = copair-cong (idIso (in₁ ∘ id C)) (initial-iso _ _) ∙
    copair-post (id C) (initiate C) in₁

  cospan : CospanMap (in₂ {C} {D}) H in₂ in₁
  cospan = record
    { left = id D ; right = unit ; base = id (C ⊔ D)
    ; leftSquare = invIso (comp-unitˡ in₂) ∙ comp-unitʳ in₂
    ; rightSquare = invIso (comp-unitˡ H) ∙ comparison }
  module F = CospanMap cospan
  module E = CospanEquivalence cospan (id-isEquiv D) (coproduct-unitʳ-isEquiv C) (id-isEquiv (C ⊔ D))

  isPullback : IsPullback (disjointCone C D)
  isPullback = equiv-transport (initial-iso _ _)
    (equiv-compose (pbLift (coproductSquare₂ (id C) (initiate D))) F.pullbackMap
      (inclusion₂-isPullback (id C) (initiate D)) E.pullbackMap-isEquiv)

disjoint-isPullback : (C D : CAT) → IsPullback (disjointCone C D)
disjoint-isPullback = Disjointness.isPullback
```
