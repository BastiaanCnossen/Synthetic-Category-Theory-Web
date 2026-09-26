# Comparing the canonical core inclusions

The core functor is postcomposition on `Map One`. Its inclusion is
natural, and naming an absolute object lifts that very object. These
comparisons let the interval-core axiom be used without adding a closure
axiom for the primitive anima predicate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M public

coreInclusion-natural : {C D : CAT} (f : MAP C D) →
  (coreInclusion D ∘ mapPost f) =₁ (f ∘ coreInclusion C)
coreInclusion-natural {C} f = comp-assoc (product-unitʳ-inverse (Core C)) mapEval f ∙
  ((mapPost-β f ▷ product-unitʳ-inverse (Core C)) ∙ (core-evaluation (mapPost f)) ⁻¹)

coreInclusion-name : {C : CAT} (x : Obj-abs C) → (coreInclusion C ∘ nameMap x) =₁ x
coreInclusion-name x = decode-name x ∙
  ((mapUncurry (nameMap x) ◁ pair-cong (terminal-iso _ _) (terminal-iso _ _)) ∙
    (core-evaluation (nameMap x)) ⁻¹)

core-inclusion-of-equivalent-anima : {C D : CAT} (f : MAP C D) →
  IsEquiv f → isAn D → IsEquiv (coreInclusion C)
core-inclusion-of-equivalent-anima {C} {D} f ef dAn =
  equiv-cancel-left (coreInclusion C) f ef
    (equiv-transport (coreInclusion-natural f)
      (equiv-compose (mapPost f) (coreInclusion D) (mapPost-isEquiv f ef) (core-of-anima D dAn)))
```
