# Cores of coproducts

For `lem:Groupoid_Core_Preserves_Disjoint_Unions`, apply `Map One` to
the coproduct universality squares and then use descent. The base case
uses the interval-core clause: the core inclusions of `One` and
`One ⊔ One` are equivalences. Recognition is not needed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalCore as Interval

module SCT.VolumeI.Chapter02.Section01.CoreCoproducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Walking.WalkingMorphism 𝒯) (K : Interval.IntervalCoreAxiom 𝒯 M B I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Universality 𝒯 M B P
open CoproductUniversality U
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.UniversalCoproductDescent 𝒯 M B P U
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
open import SCT.VolumeI.Chapter02.Section01.CoreInclusions 𝒯 M using (coreInclusion-natural)
open Interval.Consequences 𝒯 M B I K

coreCopair : (C D : CAT) → MAP (Core C ⊔ Core D) (Core (C ⊔ D))
coreCopair C D = copair (mapPost in₁) (mapPost in₂)

inclusion-copair : (C D : CAT) →
  (coreInclusion (C ⊔ D) ∘ coreCopair C D) =₁
    (coproductMap (coreInclusion C) (coreInclusion D))
inclusion-copair C D = copair-cong (coreInclusion-natural in₁) (coreInclusion-natural in₂) ∙
  copair-post (mapPost in₁) (mapPost in₂) (coreInclusion (C ⊔ D))

two-point-cover : IsEquiv (coreCopair One One)
two-point-cover = equiv-cancel-left (coreCopair One One) (coreInclusion (One ⊔ One))
  two-point-core-isEquiv (equiv-transport ((inclusion-copair One One) ⁻¹)
    (coproductMap-isEquiv (coreInclusion One) (coreInclusion One)
      (core-of-anima One one-isAn) (core-of-anima One one-isAn)))

coreCopair-isEquiv : (C D : CAT) → IsEquiv (coreCopair C D)
coreCopair-isEquiv C D = Cover.copair-isEquiv
  (mapPost in₁) (mapPost in₂) (mapPost (coproductMap (terminate C) (terminate D)))
  (mappedCone One (coproductSquare₁ (terminate C) (terminate D)))
  (mappedCone One (coproductSquare₂ (terminate C) (terminate D)))
  (map-preserves-pullback One _ (inclusion₁-isPullback (terminate C) (terminate D)))
  (map-preserves-pullback One _ (inclusion₂-isPullback (terminate C) (terminate D)))
  two-point-cover
```
