# Normalizing a triangle with an invertible leg

The inverse-comparison calculation identifies the other leg with the
inverse identification. Changing the appropriate endpoint then gives
the identity expression, including its endpoint frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.NormalizedTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.PrimitiveInverses 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionInverseLaws 𝒯 M ℱ P I E S Q
  using (inverse-comparison)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-cong; isomorphism-retarget; isomorphism-id)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)

module At {Γ C : CAT} {x y : MAP Γ C} (α : y =₁ x)
  (f : MorphismExpression x y) (g : MorphismExpression y x)
  (triangle : ExpressionIso (compose-expression f g) (identity-expression x)) where

  abstract
    normalize-counit : ExpressionIso f (isomorphism-expression (α ⁻¹)) →
      ExpressionIso (retarget-expression g α (idIso x)) (identity-expression x)
    normalize-counit unit-comparison = expressionIso-compose (isomorphism-id x)
      (expressionIso-compose
        (isomorphism-cong (isoComp-inverseʳ-at α ∙
          isoComp-cong (isoComp-unitˡ-at α) (idIso (α ⁻¹))))
        (expressionIso-compose (isomorphism-retarget α α (idIso x))
          (retarget-expressionIso counit-comparison α (idIso x))))
      where
        counit-comparison : ExpressionIso g (isomorphism-expression α)
        counit-comparison = expressionIso-inverse
          (inverse-comparison (isomorphism-expression (α ⁻¹)) (isomorphism-expression α) g
            (identification-left-inverse α)
            (expressionIso-compose triangle
              (compose-expression-cong (expressionIso-inverse unit-comparison) (expressionIso-id g))))

    normalize-unit : ExpressionIso g (isomorphism-expression α) →
      ExpressionIso (retarget-expression f (idIso x) α) (identity-expression x)
    normalize-unit counit-comparison = expressionIso-compose (isomorphism-id x)
      (expressionIso-compose
        (isomorphism-cong (isoComp-unitʳ-at (idIso x) ∙
          isoComp-cong (isoComp-inverseʳ-at α) (inverse-identity x)))
        (expressionIso-compose (isomorphism-retarget (α ⁻¹) (idIso x) α)
          (retarget-expressionIso unit-comparison (idIso x) α)))
      where
        unit-comparison : ExpressionIso f (isomorphism-expression (α ⁻¹))
        unit-comparison = inverse-comparison (isomorphism-expression α) f (isomorphism-expression (α ⁻¹))
          (expressionIso-compose triangle
            (compose-expression-cong (expressionIso-id f) (expressionIso-inverse counit-comparison)))
          (identification-left-inverse α)
```
