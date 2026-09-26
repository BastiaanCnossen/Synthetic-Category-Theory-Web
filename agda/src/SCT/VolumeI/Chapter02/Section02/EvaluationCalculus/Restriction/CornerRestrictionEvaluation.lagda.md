# Evaluating the specified corner of two restrictions

The corner matching of a family agrees with evaluating its inserted
shape corner. This comparison uses the actual restriction and evaluation
frames on both edges.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.CornerRestrictionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointConeRoutes as Routes
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionParameterEvaluation as Restrict
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointInputNaturality as Objects
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.InsertedShapeCorners as Corners
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M using (evaluate-square)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; cancel-left)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {Γ B C : CAT} (u v : Obj-abs [1]) (d k : MAP [1] B)
  (δ : (d ∘ u) =₁ (k ∘ v)) (W : MAP Γ (Fun B C)) where
  module R = Routes.At 𝒯 M ℱ I u v d k δ W
  module Shape = Corners.At 𝒯 M ℱ Γ d k u v δ
  module Left = Restrict.At 𝒯 M ℱ d W u
  module Right = Restrict.At 𝒯 M ℱ k W v
  h = funUncurry W
  L = productMap (id Γ) d
  K = productMap (id Γ) k
  iu = insert {X = Γ} u
  iv = insert {X = Γ} v
  aL = comp-assoc iu L h
  aR = comp-assoc iv K h
  left = (funPre-uncurry d W ▷ iu) ∙ evaluate-uncurry u (funPre d ∘ W)
  right = (funPre-uncurry k W ▷ iv) ∙ evaluate-uncurry v (funPre k ∘ W)
  at-left = evaluate-uncurry (d ∘ u) W
  at-right = evaluate-uncurry (k ∘ v) W
  image = h ◁ Shape.middle
  jL = (h ◁ Shape.κ) ∙ aL
  jR = (h ◁ Shape.κ′) ∙ aR
  evaluated = evaluate-square h iu K iv L Shape.comparison

  abstract
    left-square : (at-left ∙ R.left-route) =₂ (jL ∙ left)
    left-square = (isoComp-assoc-at (h ◁ Shape.κ) aL left) ⁻¹ ∙ Left.comparison
    right-square : (at-right ∙ R.right-route) =₂ (jR ∙ right)
    right-square = (isoComp-assoc-at (h ◁ Shape.κ′) aR right) ⁻¹ ∙ Right.comparison

    vertex-square : (at-right ∙ (R.vertex ▷ W)) =₂ (image ∙ at-left)
    vertex-square = Objects.EvaluationObject.natural 𝒯 M ℱ W δ

    family-square : (jR ∙ (right ∙ R.matching)) =₂ (image ∙ (jL ∙ left))
    family-square = isoComp-cong (idIso image) left-square ∙
      isoComp-assoc-at image at-left R.left-route ∙
      isoComp-cong vertex-square (idIso R.left-route) ∙
      (isoComp-assoc-at at-right (R.vertex ▷ W) R.left-route) ⁻¹ ∙
      isoComp-cong (idIso at-right) R.clear-frames ∙
      isoComp-assoc-at at-right R.right-route R.matching ∙
      isoComp-cong (right-square ⁻¹) (idIso R.matching) ∙
      (isoComp-assoc-at jR right R.matching) ⁻¹

    shape-square : (jR ∙ evaluated) =₂ (image ∙ jL)
    shape-square = isoComp-assoc-at image (h ◁ Shape.κ) aL ∙
      isoComp-cong (postWhisker-isoComp-at h Shape.middle Shape.κ) (idIso aL) ∙
      isoComp-cong (postWhisker h ◁ cancel-inverse Shape.κ′ (Shape.middle ∙ Shape.κ)) (idIso aL) ∙
      isoComp-cong ((postWhisker-isoComp-at h Shape.κ′ Shape.comparison) ⁻¹) (idIso aL) ∙
      (isoComp-assoc-at (h ◁ Shape.κ′) (h ◁ Shape.comparison) aL) ⁻¹ ∙
      isoComp-cong (idIso (h ◁ Shape.κ′))
        (cancel-inverse aR ((h ◁ Shape.comparison) ∙ aL)) ∙
      isoComp-assoc-at (h ◁ Shape.κ′) aR evaluated

    comparison : (right ∙ R.matching) =₂ (evaluated ∙ left)
    comparison = cancel-left-reflect jR
      (isoComp-assoc-at jR evaluated left ∙
        isoComp-cong (shape-square ⁻¹) (idIso left) ∙
        (isoComp-assoc-at image jL left) ⁻¹ ∙ family-square)
```
