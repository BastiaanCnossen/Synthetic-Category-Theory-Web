# Directed evaluation for equivalences

For `lem:Directed_Evaluation_for_Trivial_Fibration`, the projection to
the arrow category is a base change of a product of equivalences.
Its composite with directed evaluation is postcomposition by the original
equivalence. The two-out-of-three property proves both assertions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.Equivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (pullback-equivalence)

module EquivalenceFibration {A B : CAT} (f : MAP A B) (e : IsEquiv f) where
  open Evaluation f

  left-fibration : IsEquiv directed-ev₀
  left-fibration = equiv-cancel-left directed-ev₀ Left.diagram
    (pullback-equivalence endpoints (productMap f (id B))
      (productMap-isEquiv f (id B) e (id-isEquiv B)))
    (equiv-transport (directed-ev₀-image ⁻¹) (funPost-isEquiv f e))

  right-fibration : IsEquiv directed-ev₁
  right-fibration = equiv-cancel-left directed-ev₁ Right.diagram
    (pullback-equivalence endpoints (productMap (id B) f)
      (productMap-isEquiv (id B) f (id-isEquiv B) e))
    (equiv-transport (directed-ev₁-image ⁻¹) (funPost-isEquiv f e))
```
