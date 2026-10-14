# Evaluation and a specified isomorphism of functors

An isomorphism of functors induces an isomorphism of postcomposition
functors. Its evaluation equation is retained, so evaluation squares can
be transported along the original isomorphism with their full matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.EvaluationIsomorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality as Natural
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Along {T A B : CAT} {f g : MAP A B} (α : f =₁ g) where
  F = funPost {C = T} f
  G = funPost {C = T} g
  βf = funPost-β {C = T} f
  βg = funPost-β {C = T} g
  δ = α ▷ funEval {C = T} {D = A}
  lifted : funUncurry F =₁ funUncurry G
  lifted = βg ⁻¹ ∙ (δ ∙ βf)

  comparison : F =₁ G
  comparison = funIsoReflect F G lifted

  module At (v : Obj-abs T) where
    i = insert {X = Fun T A} v
    ef = evaluate-uncurry v F
    eg = evaluate-uncurry v G
    af = comp-assoc i funEval f
    ag = comp-assoc i funEval g

    abstract
      reflected : (((βg ▷ i) ∙ eg) ∙ (evaluate v ◁ comparison)) =₂
        ((δ ▷ i) ∙ ((βf ▷ i) ∙ ef))
      reflected = isoComp-assoc-at (δ ▷ i) (βf ▷ i) ef ∙
        isoComp-cong (preWhisker-isoComp-at δ βf i) (idIso ef) ∙
        isoComp-cong
          ((preWhisker i ◁ (cancel-inverse βg (δ ∙ βf) ∙
            isoComp-cong (idIso βg) (funIsoReflect-β F G lifted))) ∙
            (preWhisker-isoComp-at βg (funUncurryIso comparison) i) ⁻¹)
          (idIso ef) ∙
        (isoComp-assoc-at (βg ▷ i) (funUncurryIso comparison ▷ i) ef) ⁻¹ ∙
        isoComp-cong (idIso (βg ▷ i)) (Natural.Evaluation.natural 𝒯 M ℱ v comparison) ∙
        isoComp-assoc-at (βg ▷ i) eg (evaluate v ◁ comparison)

      endpoint : (evaluate-post v g ∙ (evaluate v ◁ comparison)) =₂
        ((α ▷ evaluate v) ∙ evaluate-post v f)
      endpoint = isoComp-assoc-at (α ▷ evaluate v) af ((βf ▷ i) ∙ ef) ∙
        isoComp-cong (preWhisker-comp-at α funEval i) (idIso ((βf ▷ i) ∙ ef)) ∙
        (isoComp-assoc-at ag (δ ▷ i) ((βf ▷ i) ∙ ef)) ⁻¹ ∙
        isoComp-cong (idIso ag) reflected ∙
        isoComp-assoc-at ag ((βg ▷ i) ∙ eg) (evaluate v ◁ comparison)
```
