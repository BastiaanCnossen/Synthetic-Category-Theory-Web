# Recovering an expression from the universal arrow

Restrict the universal arrow along an expression's arrow functor, then
restore its endpoint frames. The left unitor compares the result with
the original expression, including both prescribed endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.UniversalArrowSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles as Units
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) where
  module F = MorphismExpression f
  module U = Units.Universal 𝒯 M ℱ P I E C
  value = retarget-expression (restrict-expression U.arrow F.arrow) F.source-frame F.target-frame

  abstract
    endpoint : (v : MAP (Ar C) C) {z : MAP Γ C} (b : (v ∘ F.arrow) =₁ z) →
      (b ∙ (v ◁ comp-unitˡ F.arrow)) =₂
        (b ∙ ((comp-unitʳ v ▷ F.arrow) ∙ (comp-assoc F.arrow (id (Ar C)) v) ⁻¹))
    endpoint v b = isoComp-cong (idIso b)
      ((cancel-right (comp-assoc F.arrow (id (Ar C)) v) (v ◁ comp-unitˡ F.arrow) ∙
        isoComp-cong (triangle-whiskered F.arrow v) (idIso _)) ⁻¹)

  comparison : ExpressionIso value f
  comparison = record
    { comparison = comp-unitˡ F.arrow
    ; source-compatible = endpoint ev₀ F.source-frame
    ; target-compatible = endpoint ev₁ F.target-frame }
```
