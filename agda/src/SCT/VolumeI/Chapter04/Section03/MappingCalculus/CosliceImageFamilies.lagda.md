# Functorial images on coslice families

The image of the universal coslice arrow defines a functor on coslices.
We compare it with the source-endpoint construction and compute its action
on arbitrary families, retaining the complete endpoint cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (ConeIso; conePre; coneIso-compose; coneIso-inverse)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceImages as Images
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction as Restriction
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifting
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageExpressions as ActualImage
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressionCones as ExpressionCones
import SCT.VolumeI.Chapter04.Section03.CosliceFunctors as Actual
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open Laws.PullbackStructure P using (pullbackCone)

module At {C D : CAT} (F : MAP C D) (x : Obj-abs C) where
  private
    module Source = Reading.At 𝒯 M ℱ P I x using (universal; read)
    module Lift = Lifting.At 𝒯 M ℱ P I (F ∘ x) using (module Restrict; module Change)
    q = coslice-projection x
  image : MorphismExpression (const (F ∘ x)) (F ∘ q)
  image = Images.image 𝒯 M ℱ I F Source.universal

  functor : MAP (Coslice C x) (Coslice D (F ∘ x))
  functor = coslice-intro (F ∘ x) (F ∘ q) image

  module Standard where
    private
      module Original = Actual.Image 𝒯 M ℱ P I F x using (functor)
      module Formula = ActualImage.Image 𝒯 M ℱ P I F x using (projection; expression-computation)
      module Read = ExpressionCones.At.Along 𝒯 M ℱ P I (F ∘ x)
        Original.functor (F ∘ q) image Formula.projection Formula.expression-computation using (comparison)
      module H = EndpointFiber (const (F ∘ x)) (id D)
    original = Original.functor
    specified-comparison = coneIso-compose (coneIso-inverse (H.lift-β (F ∘ q)
      (retarget-expression image ((const-pre (F ∘ x) (F ∘ q)) ⁻¹) ((comp-unitˡ (F ∘ q)) ⁻¹)))) Read.comparison
    private
      module Reflected = Reflection.Lift 𝒯 P
        {f = endpoints} {g = pair (const {P = D} (F ∘ x)) (id D)}
        original functor specified-comparison using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)

  module AtFamily {Γ : CAT} (h : MAP Γ (Coslice C x)) where
    family-image : MorphismExpression (const {P = Γ} (F ∘ x)) (F ∘ (q ∘ h))
    family-image = Images.image 𝒯 M ℱ I F (Source.read h)
    private
      normalized = Restriction.restrict 𝒯 M ℱ I image h
      raw = restrict-expression image h
      α = const-pre (F ∘ x) h
      σ = comp-assoc h q F
      module ImageRestriction = Images.Restrict 𝒯 M ℱ I F Source.universal h using (comparison)
      abstract
        expression-comparison : ExpressionIso
          (retarget-expression normalized (idIso (const {P = Γ} (F ∘ x))) σ) family-image
        expression-comparison = expressionIso-compose ImageRestriction.comparison
          (expressionIso-compose (retarget-cong raw (isoComp-unitˡ-at α) (isoComp-unitʳ-at σ))
            (retarget-assoc raw α (idIso ((F ∘ q) ∘ h)) (idIso (const (F ∘ x))) σ))
      module Restricted = Lift.Restrict (F ∘ q) image h using (specified-comparison; source-projection; target-projection; base-computation)
      module Changed = Lift.Change {Γ = Γ} {b = (F ∘ q) ∘ h} {d = F ∘ (q ∘ h)}
        normalized family-image σ expression-comparison using (specified-comparison; source-projection; target-projection; base-computation)

    specified-comparison : ConeIso
      (conePre (functor ∘ h) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
      (conePre (coslice-intro (F ∘ x) (F ∘ (q ∘ h)) family-image)
        (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
    specified-comparison = coneIso-compose Changed.specified-comparison Restricted.specified-comparison
    source-projection = σ ∙ Restricted.source-projection
    target-projection = Changed.target-projection
    abstract
      base-computation : (target-projection ∙ ConeIso.rightIso specified-comparison) =₂ source-projection
      base-computation = isoComp-cong (idIso σ) Restricted.base-computation ∙
        isoComp-assoc-at σ Restricted.target-projection (ConeIso.rightIso Restricted.specified-comparison) ∙
        isoComp-cong Changed.base-computation (idIso (ConeIso.rightIso Restricted.specified-comparison)) ∙
        (isoComp-assoc-at target-projection (ConeIso.rightIso Changed.specified-comparison)
          (ConeIso.rightIso Restricted.specified-comparison)) ⁻¹
    private
      module Reflected = Reflection.Lift 𝒯 P
        {f = endpoints} {g = pair (const {P = D} (F ∘ x)) (id D)}
        (functor ∘ h) (coslice-intro (F ∘ x) (F ∘ (q ∘ h)) family-image)
        specified-comparison using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)
```
