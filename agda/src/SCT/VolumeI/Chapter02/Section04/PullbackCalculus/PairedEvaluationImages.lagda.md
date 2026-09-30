# Coordinates of paired evaluation images

Mapping an evaluation fiber along a functor postcomposes its two decoded
endpoint boundaries. The target family may carry an arbitrary specified
comparison with the image family. Both formulas retain that comparison
and use the actual matching of the paired evaluation square.

These are computations on specified cone matchings. They do not yet
identify the induced functor between hom fibers with `hom-post`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.PairedEvaluationImages
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse; pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.BoundaryTransport 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯 using (project-transport)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter01.Section06.Cospans.PairedSquares as Squares
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberImages as Images

private
  abstract
    inverse-evaluation-square : {X T C D : CAT} (z : Obj-abs T)
      (F : MAP C D) (p : MAP X (Fun T C)) →
      (comp-assoc p (funPost F) (evaluate z) ∙
        (((evaluate-post z F) ⁻¹ ▷ p) ∙ (comp-assoc p (evaluate z) F) ⁻¹)) =₂
      (evaluate-post-at z F p) ⁻¹
    inverse-evaluation-square z F p = normalized-inverse ⁻¹ ∙
      isoComp-cong (idIso (comp-assoc p (funPost F) (evaluate z)))
        (isoComp-cong (pre-inverse (evaluate-post z F) p)
          (idIso ((comp-assoc p (evaluate z) F) ⁻¹)))
      where
      normalized-inverse : (evaluate-post-at z F p) ⁻¹ =₂
        (comp-assoc p (funPost F) (evaluate z) ∙
          (((evaluate-post z F ▷ p) ⁻¹) ∙ (comp-assoc p (evaluate z) F) ⁻¹))
      normalized-inverse = isoComp-assoc-at
        (comp-assoc p (funPost F) (evaluate z))
        ((evaluate-post z F ▷ p) ⁻¹) ((comp-assoc p (evaluate z) F) ⁻¹) ∙
        (isoComp-cong
          (isoComp-cong (inverse-inverse (comp-assoc p (funPost F) (evaluate z)))
            (idIso ((evaluate-post z F ▷ p) ⁻¹)) ∙
            inverse-composite (evaluate-post z F ▷ p)
              ((comp-assoc p (funPost F) (evaluate z)) ⁻¹))
          (idIso ((comp-assoc p (evaluate z) F) ⁻¹)) ∙
          inverse-composite (comp-assoc p (evaluate z) F)
            ((evaluate-post z F ▷ p) ∙ (comp-assoc p (funPost F) (evaluate z)) ⁻¹))

module Along {T C D Γ : CAT} (z₀ z₁ : Obj-abs T) (F : MAP C D)
  (family : MAP Γ (C × C)) (target : MAP Γ (D × D))
  (δ : (productMap F F ∘ family) =₁ target) where
  private
    module Square = Squares.Pair 𝒯 (funPost {C = T} F) F F
      (evaluate z₀) (evaluate z₁) (evaluate z₀) (evaluate z₁)
      ((evaluate-post z₀ F) ⁻¹) ((evaluate-post z₁ F) ⁻¹)
      using (matching; first-restriction; second-restriction)
    module Product = Products.Coordinates 𝒯 F F F F using (module First; module Second)
    module Image = Images.Along 𝒯
      (pair (evaluate z₀) (evaluate z₁)) family (funPost F)
      (pair (evaluate z₀) (evaluate z₁)) (productMap F F) target Square.matching δ
      using (value; action; restrict; left-normal; right-normal)
  open Image public using (value; action; restrict; left-normal; right-normal)

  abstract
    first-boundary : {X : CAT} (q : Cone (pair (evaluate z₀) (evaluate z₁)) family X) →
      ((pr₁ ◁ Cone.match (value q)) ∙
        (project-pair₁ (evaluate z₀) (evaluate z₁) (funPost F ∘ Cone.left q)) ⁻¹) =₂
      (((pr₁ ◁ right-normal (Cone.right q)) ∙
        (Product.First.left-normal (family ∘ Cone.right q)) ⁻¹) ∙
        ((F ◁ ((pr₁ ◁ Cone.match q) ∙
          (project-pair₁ (evaluate z₀) (evaluate z₁) (Cone.left q)) ⁻¹)) ∙
          evaluate-post-at z₀ F (Cone.left q)))
    first-boundary q =
      post-boundary-transport F
        (project-pair₁ (evaluate z₀) (evaluate z₁) (Cone.left q)) (pr₁ ◁ Cone.match q)
        (Product.First.left-normal (pair (evaluate z₀) (evaluate z₁) ∘ Cone.left q))
        (Product.First.left-normal (family ∘ Cone.right q))
        (pr₁ ◁ left-normal (Cone.left q)) (pr₁ ◁ right-normal (Cone.right q))
        (project-pair₁ (evaluate z₀) (evaluate z₁) (funPost F ∘ Cone.left q))
        (evaluate-post-at z₀ F (Cone.left q)) (pr₁ ◁ (productMap F F ◁ Cone.match q))
        (Square.first-restriction (Cone.left q) ∙
          isoComp-cong ((inverse-evaluation-square z₀ F (Cone.left q)) ⁻¹)
            (idIso ((F ◁ project-pair₁ (evaluate z₀) (evaluate z₁) (Cone.left q)) ∙
              Product.First.left-normal (pair (evaluate z₀) (evaluate z₁) ∘ Cone.left q))))
        (Product.First.left-natural (Cone.match q)) ∙
      isoComp-cong
        (project-transport pr₁ (left-normal (Cone.left q))
          (right-normal (Cone.right q)) (productMap F F ◁ Cone.match q))
        (idIso ((project-pair₁ (evaluate z₀) (evaluate z₁) (funPost F ∘ Cone.left q)) ⁻¹))

  abstract
    second-boundary : {X : CAT} (q : Cone (pair (evaluate z₀) (evaluate z₁)) family X) →
      ((pr₂ ◁ Cone.match (value q)) ∙
        (project-pair₂ (evaluate z₀) (evaluate z₁) (funPost F ∘ Cone.left q)) ⁻¹) =₂
      (((pr₂ ◁ right-normal (Cone.right q)) ∙
        (Product.Second.left-normal (family ∘ Cone.right q)) ⁻¹) ∙
        ((F ◁ ((pr₂ ◁ Cone.match q) ∙
          (project-pair₂ (evaluate z₀) (evaluate z₁) (Cone.left q)) ⁻¹)) ∙
          evaluate-post-at z₁ F (Cone.left q)))
    second-boundary q =
      post-boundary-transport F
        (project-pair₂ (evaluate z₀) (evaluate z₁) (Cone.left q)) (pr₂ ◁ Cone.match q)
        (Product.Second.left-normal (pair (evaluate z₀) (evaluate z₁) ∘ Cone.left q))
        (Product.Second.left-normal (family ∘ Cone.right q))
        (pr₂ ◁ left-normal (Cone.left q)) (pr₂ ◁ right-normal (Cone.right q))
        (project-pair₂ (evaluate z₀) (evaluate z₁) (funPost F ∘ Cone.left q))
        (evaluate-post-at z₁ F (Cone.left q)) (pr₂ ◁ (productMap F F ◁ Cone.match q))
        (Square.second-restriction (Cone.left q) ∙
          isoComp-cong ((inverse-evaluation-square z₁ F (Cone.left q)) ⁻¹)
            (idIso ((F ◁ project-pair₂ (evaluate z₀) (evaluate z₁) (Cone.left q)) ∙
              Product.Second.left-normal (pair (evaluate z₀) (evaluate z₁) ∘ Cone.left q))))
        (Product.Second.left-natural (Cone.match q)) ∙
      isoComp-cong
        (project-transport pr₂ (left-normal (Cone.left q))
          (right-normal (Cone.right q)) (productMap F F ◁ Cone.match q))
        (idIso ((project-pair₂ (evaluate z₀) (evaluate z₁) (funPost F ∘ Cone.left q)) ⁻¹))
```
