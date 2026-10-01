# Equivalences and changes of the total category

Every equivalence is both a left and a right fibration: in its evaluation
square both horizontal functors are equivalences. Composing with an
equivalence of total categories preserves and reflects either fibration
property. These facts allow equivalent presentations over a fixed base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.Equivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section02.Composition 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter04.Section02.IsomorphismInvariance 𝒯 M ℱ P I
  using (left-invariance; right-invariance)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)

abstract
  equivalence-isLeftFibration : {A B : CAT} (f : MAP A B) → IsEquiv f →
    IsEquiv (Evaluation.directed-ev₀ f)
  equivalence-isLeftFibration f ef = Criterion.pullback-to-left f
    (degenerate-pullback ef (Criterion.source-square f) (funPost-isEquiv f ef))

  equivalence-isRightFibration : {A B : CAT} (f : MAP A B) → IsEquiv f →
    IsEquiv (Evaluation.directed-ev₁ f)
  equivalence-isRightFibration f ef = Criterion.pullback-to-right f
    (degenerate-pullback ef (Criterion.target-square f) (funPost-isEquiv f ef))

module TotalEquivalence {A B C : CAT} (e : MAP A B) (ee : IsEquiv e) (p : MAP B C) where
  back = IsEquiv.inverse ee
  retract : ((p ∘ e) ∘ back) =₁ p
  retract = comp-unitʳ p ∙ ((p ◁ (IsEquiv.retractionIso ee) ⁻¹) ∙ comp-assoc back e p)

  abstract
    left-preserve : IsEquiv (Evaluation.directed-ev₀ p) → IsEquiv (Evaluation.directed-ev₀ (p ∘ e))
    left-preserve = left-composition e p (equivalence-isLeftFibration e ee)

    left-reflect : IsEquiv (Evaluation.directed-ev₀ (p ∘ e)) → IsEquiv (Evaluation.directed-ev₀ p)
    left-reflect h = left-invariance retract
      (left-composition back (p ∘ e) (equivalence-isLeftFibration back (equiv-inverse ee)) h)

    right-preserve : IsEquiv (Evaluation.directed-ev₁ p) → IsEquiv (Evaluation.directed-ev₁ (p ∘ e))
    right-preserve = right-composition e p (equivalence-isRightFibration e ee)

    right-reflect : IsEquiv (Evaluation.directed-ev₁ (p ∘ e)) → IsEquiv (Evaluation.directed-ev₁ p)
    right-reflect h = right-invariance retract
      (right-composition back (p ∘ e) (equivalence-isRightFibration back (equiv-inverse ee)) h)
```
