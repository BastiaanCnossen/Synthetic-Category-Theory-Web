# Absolute morphisms as hom points

Retarget an absolute morphism along the terminal constant comparisons
to obtain its hom point. The constant family of this point agrees with
restriction of the original morphism, including both endpoint frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomRestriction 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget-outer; retarget-cong; retarget-id)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantPointRestriction 𝒯 M
  using (const-One-cancel)

module AtExpression {C : CAT} {x y : Obj-abs C} (f : MorphismExpression x y) where
  normalized : MorphismExpression (const {P = One} x) (const y)
  normalized = retarget-expression f ((const-One x) ⁻¹) ((const-One y) ⁻¹)

  point : Obj-abs (Hom C x y)
  point = hom-intro normalized

  family : (Γ : CAT) → MorphismExpression (const {P = Γ} x) (const y)
  family Γ = hom-expression (const point)

  abstract
    point-comparison : ExpressionIso (hom-expression point) normalized
    point-comparison = hom-β normalized

    family-comparison : (Γ : CAT) →
      ExpressionIso (family Γ) (restrict-expression f (terminate Γ))
    family-comparison Γ = expressionIso-compose (retarget-id (restrict-expression f t))
      (expressionIso-compose
        (retarget-cong (restrict-expression f t) (const-One-cancel x) (const-One-cancel y))
        (expressionIso-compose
          (restrict-retarget-outer f ((const-One x) ⁻¹) ((const-One y) ⁻¹) t
            (const-pre x t) (const-pre y t))
          (expressionIso-compose (hom-restrict-cong point-comparison t)
            (hom-expression-restrict point t))))
      where
      t : MAP Γ One
      t = terminate Γ
```
