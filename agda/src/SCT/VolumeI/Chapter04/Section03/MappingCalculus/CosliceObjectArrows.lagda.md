# The hom-category arrow represented by a coslice object

Reading an object of a coslice gives a point of the corresponding hom
category. Its constant family agrees, with both endpoint frames, with
the family obtained directly from the universal arrow of the coslice.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceObjectArrows
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomRestriction 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget-outer; retarget-cong; retarget-assoc)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantPointRestriction 𝒯 M using (const-One-cancel)
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction as Restriction

module At {C : CAT} (x : Obj-abs C) (u : Obj-abs (Coslice C x)) where
  private
    q = coslice-projection x
    module Read = Reading.At 𝒯 M ℱ P I x using (universal; read)
    module Fixed = Restriction.Fixed 𝒯 M ℱ I Read.universal u using (family)

  y = q ∘ u
  point-expression : MorphismExpression (const {P = One} x) (const y)
  point-expression = retarget-expression (Read.read u) (idIso (const x)) ((const-One y) ⁻¹)

  point : Obj-abs (Hom C x y)
  point = hom-intro point-expression

  module Family (Γ : CAT) where
    private
      t = terminate Γ
      raw = restrict-expression (Read.read u) t
      p = const-pre x t
      source-id = idIso (const {P = Γ} x)
      target-id = idIso (const {P = Γ} y)
      A₀ = comp-assoc t u q
      γ = constant-image Γ q u
      normalized = retarget-expression raw p target-id
      module Successive = Restriction.Successive 𝒯 M ℱ I Read.universal u t using (comparison)

      abstract
        from-point : ExpressionIso (hom-restrict point-expression t) normalized
        from-point = expressionIso-compose
          (retarget-cong raw
            (isoComp-unitʳ-at p ∙ isoComp-cong (idIso p) (preWhisker-idIso (const {P = One} x) t))
            (const-One-cancel y))
          (restrict-retarget-outer (Read.read u) (idIso (const x)) ((const-One y) ⁻¹) t p (const-pre y t))

        to-family : ExpressionIso normalized (Fixed.family Γ)
        to-family = expressionIso-compose (retarget-expressionIso Successive.comparison source-id γ)
          (expressionIso-compose (expressionIso-inverse (retarget-assoc raw p A₀ source-id γ))
            (retarget-cong raw ((isoComp-unitˡ-at p) ⁻¹) ((isoComp-inverseˡ-at A₀) ⁻¹)))

    abstract
      comparison : ExpressionIso (hom-expression (const {P = Γ} point)) (Fixed.family Γ)
      comparison = expressionIso-compose to-family
        (expressionIso-compose from-point
        (expressionIso-compose (hom-restrict-cong (hom-β point-expression) t)
          (hom-expression-restrict point t)))
```
