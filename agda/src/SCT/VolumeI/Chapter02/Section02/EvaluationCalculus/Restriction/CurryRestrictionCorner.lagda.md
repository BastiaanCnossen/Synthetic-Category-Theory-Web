# Evaluating a restricted curried diagram

The retained curry beta comparison and parameter-restriction comparison
commute with endpoint evaluation. The remaining comparison is precisely
the evaluated insertion square, including the parameter associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.CurryRestrictionCorner
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionEvaluation 𝒯 M ℱ
  using (evaluate-insertion; evaluate-uncurry-compose)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M using (change-evaluation)

module At {X Y A C : CAT} (H : MAP (Y × A) C) (σ : MAP X Y) (u : Obj-abs A) where
  h = funCurry H
  β = funCurry-β H
  step = productMap σ (id A)
  ix = insert {X = X} u
  iy = insert {X = Y} u
  χ = insert-natural σ u
  q = funUncurry-restrict h σ
  raw = (β ▷ step) ∙ q
  endpoint = evaluate-uncurry u (h ∘ σ)
  old = evaluate-insertion (funUncurry h) σ u
  new = evaluate-insertion H σ u
  bV = (β ▷ step) ▷ ix
  bH = (β ▷ iy) ▷ σ
  before = evaluate-uncurry u h ▷ σ
  after = evaluate-curry u H ▷ σ
  associator = (comp-assoc σ h (evaluate u)) ⁻¹

  abstract
    comparison : ((raw ▷ ix) ∙ endpoint) =₂ ((new ∙ after) ∙ associator)
    comparison = isoComp-cong
        (isoComp-cong (idIso new) ((preWhisker-isoComp-at (β ▷ iy) (evaluate-uncurry u h) σ) ⁻¹) ∙
          isoComp-assoc-at new bH before)
        (idIso associator) ∙
      isoComp-cong (isoComp-cong ((change-evaluation β σ step ix iy χ) ⁻¹) (idIso before)) (idIso associator) ∙
      isoComp-cong ((isoComp-assoc-at bV old before) ⁻¹) (idIso associator) ∙
      (isoComp-assoc-at bV (old ∙ before) associator) ⁻¹ ∙
      isoComp-cong (idIso bV) (evaluate-uncurry-compose u h σ) ∙
      isoComp-assoc-at bV (q ▷ ix) endpoint ∙
      isoComp-cong (preWhisker-isoComp-at (β ▷ step) q ix) (idIso endpoint)
```
