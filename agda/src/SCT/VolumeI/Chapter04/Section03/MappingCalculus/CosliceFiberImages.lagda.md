# Functorial images on hom fibers of coslices

The normalized image functor on coslices restricts to the specified
hom-postcomposition functor. The comparison is constructed on complete
endpoint cones and retains the computation of its target projection.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceFiberImages
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (ConeIso; conePre; coneIso-compose; coneIso-inverse)
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceHomFibers as Fibers
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageFamilies as Families
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifting
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceImages as Images
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Laws.PullbackStructure P using (pullbackCone)

module At {C D : CAT} (F : MAP C D) (x z : Obj-abs C) where
  private
    H = Hom C x z
    module Source = Fibers.At 𝒯 M ℱ P I x z using (inclusion; projection; universal; expression-computation)
    module Target = Fibers.At 𝒯 M ℱ P I (F ∘ x) (F ∘ z) using (inclusion; module Family)
    module Image = Families.At 𝒯 M ℱ P I F x using (functor; module AtFamily)
    module First = Image.AtFamily {Γ = H} Source.inclusion using (family-image; specified-comparison; source-projection; target-projection; base-computation)
    module Last = Target.Family {Γ = H} (hom-post F x z) using (specified-comparison; source-projection; target-projection; base-computation)
    module Read = Reading.At 𝒯 M ℱ P I x using (read)
    module Lift = Lifting.At 𝒯 M ℱ P I (F ∘ x) using (module Change)
    f = Read.read {Γ = H} Source.inclusion
    V = Source.universal
    sx = idIso (const {P = H} (F ∘ x))
    γx = constant-image H F x
    γz = constant-image H F z
    t = F ◁ Source.projection
    σ = γz ∙ t
    module Frame = Images.Change 𝒯 M ℱ I F f V Source.projection Source.expression-computation using (comparison)
    abstract
      normalized-hom-image : ExpressionIso
        (retarget-expression (Images.image 𝒯 M ℱ I F V) sx γz) (hom-image F V)
      normalized-hom-image = expressionIso-compose
        (retarget-cong (post-expression F V) (isoComp-unitˡ-at γx) (isoComp-unitʳ-at γz))
        (retarget-assoc (post-expression F V) γx (idIso (F ∘ const {P = H} z)) sx γz)

      expression-comparison : ExpressionIso
        (retarget-expression First.family-image sx σ) (hom-expression (hom-post F x z))
      expression-comparison = expressionIso-compose (expressionIso-inverse (hom-post-computation F x z))
        (expressionIso-compose normalized-hom-image
        (expressionIso-compose (retarget-expressionIso Frame.comparison sx γz)
        (expressionIso-compose (expressionIso-inverse (retarget-assoc First.family-image sx t sx γz))
          (retarget-cong First.family-image ((isoComp-unitˡ-at sx) ⁻¹) (idIso σ)))))
    module Changed = Lift.Change {Γ = H}
      {b = F ∘ (coslice-projection x ∘ Source.inclusion)} {d = const {P = H} (F ∘ z)}
      First.family-image (hom-expression (hom-post F x z)) σ expression-comparison
      using (specified-comparison; source-projection; target-projection; base-computation)

  image = Image.functor
  hom-image-map = hom-post F x z
  source-inclusion = Source.inclusion
  target-inclusion = Target.inclusion

  specified-comparison : ConeIso
    (conePre (image ∘ source-inclusion) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
    (conePre (target-inclusion ∘ hom-image-map) (pullbackCone endpoints (pair (const (F ∘ x)) (id D))))
  specified-comparison = coneIso-compose (coneIso-inverse Last.specified-comparison)
    (coneIso-compose Changed.specified-comparison First.specified-comparison)
  private
    module Reflected = Reflection.Lift 𝒯 P
      {f = endpoints} {g = pair (const {P = D} (F ∘ x)) (id D)}
      (image ∘ source-inclusion) (target-inclusion ∘ hom-image-map) specified-comparison
      using (lift; comparison-image; left-image; right-image)
  open Reflected public renaming (lift to comparison)

  source-projection = σ ∙ First.source-projection
  target-projection = Last.source-projection
  private
    first = ConeIso.rightIso First.specified-comparison
    changed = ConeIso.rightIso Changed.specified-comparison
    last = ConeIso.rightIso Last.specified-comparison
    β = Last.target-projection
    abstract
      last-cancel : (target-projection ∙ last ⁻¹) =₂ β
      last-cancel = cancel-right last β ∙ isoComp-cong (Last.base-computation ⁻¹) (idIso (last ⁻¹))
  abstract
    base-computation : (target-projection ∙ ConeIso.rightIso specified-comparison) =₂ source-projection
    base-computation = isoComp-cong (idIso σ) First.base-computation ∙
      isoComp-assoc-at σ First.target-projection first ∙
      isoComp-cong Changed.base-computation (idIso first) ∙
      (isoComp-assoc-at β changed first) ⁻¹ ∙
      isoComp-cong last-cancel (idIso (changed ∙ first)) ∙
      (isoComp-assoc-at target-projection (last ⁻¹) (changed ∙ first)) ⁻¹
```
