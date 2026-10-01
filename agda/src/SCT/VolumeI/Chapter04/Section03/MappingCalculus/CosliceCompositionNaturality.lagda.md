# Composition squares for functors on coslices

A functor carries composition with a fixed morphism to composition with
its image. Both routes are compared with the same normalized composite
family. Reflection retains the complete endpoint comparison, including
the selected matching of the square.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceCompositionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition 𝒯 M ℱ P I using (hom-image)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S using (post-composition)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; conePre; coneIso-compose; coneIso-inverse)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceImages as Images
import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomCompositionNaturality as HomNaturality
import SCT.VolumeI.Chapter04.Section03.CoslicePrecomposition as OriginalPrecomposition
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CoslicePrecompositionFamilies as Precomposition
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageFamilies as ImageFamilies
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressionCones as ExpressionCones
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifting
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open Laws.PullbackStructure P using (pullbackCone)

abstract
  image-composition : {Γ C D : CAT} (F : MAP C D) {x y : Obj-abs C} {q : MAP Γ C}
    (f : MorphismExpression (const {P = Γ} x) (const y))
    (g : MorphismExpression (const y) q) →
    ExpressionIso (Images.image 𝒯 M ℱ I F (compose-expression f g))
      (compose-expression (hom-image F f) (Images.image 𝒯 M ℱ I F g))
  image-composition {Γ} F {x} {y} {q} f g = expressionIso-inverse
    (expressionIso-compose (retarget-expressionIso (post-composition F f g)
      (constant-image Γ F x) (idIso (F ∘ q)))
      (retarget-composition (post-expression F f) (post-expression F g)
        (constant-image Γ F x) (constant-image Γ F y) (idIso (F ∘ q))))

module Along {C D : CAT} (F : MAP C D) {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  private
    Γ = Coslice C y
    module Original = OriginalPrecomposition.Along 𝒯 M ℱ P I E S {C = C} {x = x} {y = y} e
      using (functor; composite; computation)
    module XImage = ImageFamilies.At 𝒯 M ℱ P I F x using (functor; module AtFamily)
    module YImage = ImageFamilies.At 𝒯 M ℱ P I F y using (functor; image)
    module OriginalArrow = At {C = C} {x = x} {y = y} e using (family)
    module MappedArrow = HomNaturality.Image 𝒯 M ℱ P I E S {C = C} {D = D} F {x = x} {y = y} e using (point; family-comparison)
    module Mapped = Precomposition.ForArrow 𝒯 M ℱ P I E S
      {C = D} {x = F ∘ x} {y = F ∘ y} MappedArrow.point using (functor; module AtFamily)
    module MappedFamily = At {C = D} {x = F ∘ x} {y = F ∘ y} MappedArrow.point using (family)
    module XRead = Reading.At 𝒯 M ℱ P I x using (read)
    module YRead = Reading.At 𝒯 M ℱ P I y using (universal)
    module DYRead = Reading.At 𝒯 M ℱ P I (F ∘ y) using (read)
    module LeftFamily = XImage.AtFamily {Γ = Γ} Original.functor using (family-image; specified-comparison)
    module RightFamily = Mapped.AtFamily {Γ = Γ} YImage.functor using (composite; specified-comparison)
    module Lift = Lifting.At 𝒯 M ℱ P I (F ∘ x) using (module Change)
    module OriginalComputation = ExpressionCones.At.FromCone 𝒯 M ℱ P I x
      Original.functor (coslice-projection y) Original.composite Original.computation using (projection; comparison)
    module YLift = EndpointFiber (const {P = D} (F ∘ y)) (id D)
    q = coslice-projection y
    framed-image = retarget-expression YImage.image ((const-pre (F ∘ y) (F ∘ q)) ⁻¹) ((comp-unitˡ (F ∘ q)) ⁻¹)
    module ImageComputation = ExpressionCones.At.FromCone 𝒯 M ℱ P I (F ∘ y)
      YImage.functor (F ∘ q) YImage.image (YLift.lift-β (F ∘ q) framed-image) using (projection; comparison)
    module ChangedImage = Images.Change 𝒯 M ℱ I F (XRead.read {Γ = Γ} Original.functor)
      Original.composite OriginalComputation.projection OriginalComputation.comparison using (comparison)
    sx = idIso (const {P = Γ} (F ∘ x))
    sy = idIso (const {P = Γ} (F ∘ y))
    f = OriginalArrow.family Γ
    g = YRead.universal
    mf = MappedFamily.family Γ
    mg = DYRead.read {Γ = Γ} YImage.functor

  common : MorphismExpression (const {P = Γ} (F ∘ x)) (F ∘ q)
  common = compose-expression mf YImage.image
  private
    abstract
      left-expression : ExpressionIso
        (retarget-expression LeftFamily.family-image sx (F ◁ OriginalComputation.projection)) common
      left-expression = expressionIso-compose
        (compose-expression-cong
          {f = hom-image F f} {f′ = mf} {g = YImage.image} {g′ = YImage.image}
          (MappedArrow.family-comparison Γ) (expressionIso-id YImage.image))
        (expressionIso-compose (image-composition F f g) ChangedImage.comparison)
      right-expression : ExpressionIso
        (retarget-expression RightFamily.composite sx ImageComputation.projection) common
      right-expression = expressionIso-compose
        (compose-expression-cong
          {f = retarget-expression mf sx sy} {f′ = mf}
          {g = retarget-expression mg sy ImageComputation.projection} {g′ = YImage.image}
          (retarget-id mf) ImageComputation.comparison)
        (expressionIso-inverse (retarget-composition mf mg sx sy ImageComputation.projection))
    module LeftChanged = Lift.Change {Γ = Γ}
      {b = F ∘ (coslice-projection x ∘ Original.functor)} {d = F ∘ q}
      LeftFamily.family-image common (F ◁ OriginalComputation.projection) left-expression using (specified-comparison)
    module RightChanged = Lift.Change {Γ = Γ}
      {b = coslice-projection (F ∘ y) ∘ YImage.functor} {d = F ∘ q}
      RightFamily.composite common ImageComputation.projection right-expression using (specified-comparison)

  image-source = XImage.functor
  image-target = YImage.functor
  precompose = Original.functor
  image-precompose = Mapped.functor
  left-comparison : ConeIso
    (conePre (image-source ∘ precompose) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
    (conePre (coslice-intro (F ∘ x) (F ∘ q) common) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
  left-comparison = coneIso-compose LeftChanged.specified-comparison LeftFamily.specified-comparison
  right-comparison : ConeIso
    (conePre (image-precompose ∘ image-target) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
    (conePre (coslice-intro (F ∘ x) (F ∘ q) common) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
  right-comparison = coneIso-compose RightChanged.specified-comparison RightFamily.specified-comparison

  specified-comparison : ConeIso
    (conePre (image-source ∘ precompose) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
    (conePre (image-precompose ∘ image-target) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
  specified-comparison = coneIso-compose (coneIso-inverse right-comparison) left-comparison
  private
    module Reflected = Reflection.Lift 𝒯 P
      {f = endpoints} {g = pair (const {P = D} (F ∘ x)) (id D)}
      (image-source ∘ precompose) (image-precompose ∘ image-target) specified-comparison
      using (lift; comparison-image; left-image; right-image)
  open Reflected public renaming (lift to comparison)

  square : Cone image-source image-precompose Γ
  square = record { left = precompose ; right = image-target ; match = comparison }
```
