# Product reassociation compares the full parameter cones

Forget the external parameter and use the projection comparison for
fiberwise reassociation. Lift its left leg back to the product with the
parameter, retaining its prescribed second projection. This recovers
the full cone comparison with the reassociation triangle as right leg.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductParameterCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse; coneIso-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change; coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone; compositeCone-pre; compositeCone-compatible)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module FirstFactor)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.FamilyProjection 𝒯 M ℱ P using (projection)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedCones 𝒯 using (module Parameter)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductUncurryingTriangles 𝒯 M ℱ P using (module Product)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ProductTriangleCones 𝒯 M ℱ P using (module Triangle)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductFamilyReassociation 𝒯 M ℱ P using (module Regroup)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductFamilyProjection 𝒯 M ℱ P using (module Projection)
open import SCT.VolumeI.Chapter03.Section05.Currying.ConeRestrictionTriangles 𝒯 M ℱ P using (module Restrict)

module Parameters {T S E K : CAT} (r : MAP E (T × S)) (k : MAP K T) (X : CAT) where
  module R = Regroup r k X
  module ProductProjection = Projection r k X
  module C = Triangle S (projection k X)
  module Param = Parameter X (FirstFactor.square k S)
  J = R.argument
  regroup = FunctorLift.lift J
  inner = FirstFactor.square R.k′ S
  base = FirstFactor.square k S
  original = compositeCone (pr₂ {X} {K}) k inner
  acted = Action.value R.F.projection (projection k X) inner
  source = conePre regroup inner
  target = Param.cone

  abstract
    original-matching : Cone.match original =₂ Cone.match acted
    original-matching = isoComp-cong (idIso (Cone.match inner))
      ((isoComp-unitˡ-at ((comp-assoc (pr₁ {X × K} {S}) (pr₂ {X} {K}) k) ⁻¹) ∙
        isoComp-cong (preWhisker-idIso R.k′ (pr₁ {X × K} {S}))
          (idIso ((comp-assoc (pr₁ {X × K} {S}) (pr₂ {X} {K}) k) ⁻¹))) ⁻¹)

  normalize = cone-match-change _ _ _ _ original-matching
  module Reduced = Restrict base acted (Product.value S (projection k X)) C.comparison C.right-image
    (pr₂ {X} {K × S}) J ProductProjection.comparison
  start = coneIso-compose (coneIso-pre regroup normalize)
    (coneIso-inverse (compositeCone-pre (pr₂ {X} {K}) k regroup inner))
  finish = coneIso-compose (coneIso-inverse Param.projection) Reduced.value
  projected = coneIso-compose finish start
  source-right = Cone.right source
  target-right = Cone.right target

  abstract
    start-right : ConeIso.rightIso start =₂ idIso source-right
    start-right = isoComp-unitˡ-at (idIso source-right) ∙
      isoComp-cong (preWhisker-idIso (Cone.right inner) regroup) (inverse-identity source-right)

    finish-right : ConeIso.rightIso finish =₂ FunctorLift.comparison J
    finish-right = isoComp-unitˡ-at (FunctorLift.comparison J) ∙
      isoComp-cong (inverse-identity target-right) Reduced.right-image

    right-image : ConeIso.rightIso projected =₂ FunctorLift.comparison J
    right-image = isoComp-unitʳ-at (FunctorLift.comparison J) ∙ isoComp-cong finish-right start-right

  first-source = Associativity.backward-first X K S ∙
    (comp-assoc regroup (pr₁ {X × K} {S}) (pr₁ {X} {K})) ⁻¹
  first-target = comp-unitˡ (pr₁ {X} {K × S}) ∙
    pair-β₁ (id X ∘ pr₁) ((pr₁ {K} {S}) ∘ pr₂)
  first = first-target ⁻¹ ∙ first-source
  second = ConeIso.leftIso projected
  left = pair-iso first second
  adjusted = coneIso-adjust projected ((pr₂ {X} {K}) ◁ left) (FunctorLift.comparison J)
    ((pair-iso-β₂ first second) ⁻¹) right-image

  comparison : ConeIso source target
  comparison = compositeCone-compatible (pr₂ {X} {K}) k source target left (FunctorLift.comparison J)
    (ConeIso.compatible adjusted)
```
