# Cancelling a change of the left cospan

Changing the structure of a relative functor and the left cospan of
its input cone by the same identification cancels in their composite.
The resulting cone comparison fixes both legs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section05.Currying.ChangedConeAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (change-source)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module Changed {A B S T X : CAT} {f f′ : MAP A T} {g : MAP B T} (p : MAP S T)
  (α : f =₁ f′) (u : FunctorOver f g) (s : Cone f p X) where
  l = Cone.left s
  τ = Cone.match s
  θ = FunctorLift.comparison u ▷ l
  δ = α ▷ l
  assoc = comp-assoc l (FunctorLift.lift u) g
  source = Action.value p (change-source α u) (changeLeft α s)
  target = Action.value p u s

  abstract
    matching : Cone.match source =₂ Cone.match target
    matching = isoComp-cong (idIso τ) (cancel-left δ (θ ∙ assoc ⁻¹)) ∙
      (isoComp-assoc-at τ (δ ⁻¹) (δ ∙ (θ ∙ assoc ⁻¹)) ∙
        (isoComp-cong (idIso (τ ∙ δ ⁻¹)) (isoComp-assoc-at δ θ (assoc ⁻¹)) ∙
          isoComp-cong (idIso (τ ∙ δ ⁻¹))
            (isoComp-cong (preWhisker-isoComp-at α (FunctorLift.comparison u) l) (idIso (assoc ⁻¹)))))

  comparison : ConeIso source target
  comparison = cone-match-change _ _ _ _ matching
```
