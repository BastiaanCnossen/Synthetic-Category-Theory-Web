# Computing the underlying functor of a relative mapping point

A functor between relative functor categories acts on their cores.
If its evaluated family is postcomposition by `k`, its action on an
absolute mapping point decodes to postcomposition by `k` as well.
This theorem computes underlying functors. Compatibility with the
triangles is a separate, stronger comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointComputations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
  using (Core; coreInclusion; coreInclusion-natural)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ using (decodeFun-cong)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.DecodedFamilies 𝒯 M ℱ using (at-point; family-at-point)

module Postcomposition {B C D S : CAT} (f : MAP B S) (g : MAP C S) (h : MAP D S)
  (k : MAP C D) (F : MAP (FunOver f g) (FunOver f h))
  (β : funUncurry (Over.forget f h ∘ F) =₁ (k ∘ funUncurry (Over.forget f g))) where

  abstract
    comparison : (x : Obj-abs (MapOver f g)) →
      FunctorLift.lift (Over.decode-over f h (mapPost F ∘ x)) =₁
        (k ∘ FunctorLift.lift (Over.decode-over f g x))
    comparison x = (k ◁ (Over.decode-underlying f g x) ⁻¹) ∙
      (at-point (Over.forget f h ∘ F) (Over.forget f g) k β object ∙
        (decodeFun-cong names ∙ Over.decode-underlying f h (mapPost F ∘ x)))
      where
      object : Obj-abs (FunOver f g)
      object = coreInclusion (FunOver f g) ∘ x
      cores : (coreInclusion (FunOver f h) ∘ (mapPost F ∘ x)) =₁ (F ∘ object)
      cores = comp-assoc x (coreInclusion (FunOver f g)) F ∙
        ((coreInclusion-natural F ▷ x) ∙
          (comp-assoc x (mapPost F) (coreInclusion (FunOver f h))) ⁻¹)
      names : (Over.forget f h ∘ (coreInclusion (FunOver f h) ∘ (mapPost F ∘ x))) =₁
        ((Over.forget f h ∘ F) ∘ object)
      names = (comp-assoc object F (Over.forget f h)) ⁻¹ ∙ (Over.forget f h ◁ cores)

module Family {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (F : MAP X (FunOver f g)) where

  parameter : Obj-abs (Core X) → MAP C (X × C)
  parameter x = productMap (coreInclusion X ∘ x) (id C) ∘ oneProduct-in C

  abstract
    comparison : (x : Obj-abs (Core X)) →
      FunctorLift.lift (Over.decode-over f g (mapPost F ∘ x)) =₁
        (funUncurry (Over.forget f g ∘ F) ∘ parameter x)
    comparison x = family-at-point (Over.forget f g ∘ F) object ∙
      (decodeFun-cong names ∙ Over.decode-underlying f g (mapPost F ∘ x))
      where
      object : Obj-abs X
      object = coreInclusion X ∘ x
      cores : (coreInclusion (FunOver f g) ∘ (mapPost F ∘ x)) =₁ (F ∘ object)
      cores = comp-assoc x (coreInclusion X) F ∙
        ((coreInclusion-natural F ▷ x) ∙
          (comp-assoc x (mapPost F) (coreInclusion (FunOver f g))) ⁻¹)
      names : (Over.forget f g ∘ (coreInclusion (FunOver f g) ∘ (mapPost F ∘ x))) =₁
        ((Over.forget f g ∘ F) ∘ object)
      names = (comp-assoc object F (Over.forget f g)) ⁻¹ ∙ (Over.forget f g ◁ cores)
```
