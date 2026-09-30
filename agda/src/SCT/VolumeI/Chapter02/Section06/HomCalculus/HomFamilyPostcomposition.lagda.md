# Hom postcomposition with specified family identifications

The source and target endpoint families may be represented by arbitrary
functors into the products. Specified identifications with paired endpoints
conjugate their fiber-image map to the existing hom-post functor. The
compatibility of these identifications with the image-family comparison
is supplied explicitly. The complete conjugation square is retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomFamilyPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  vocabulary terminal products productLaws composition vertical whiskering using (productMap-pair)
import SCT.VolumeI.Chapter01.Section06.Cospans.PairedSquares as Squares
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberImageFamilyChange as Changes
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences as Families
import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomFiberPostcomposition as HomImages
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Lifting
open Laws.PullbackStructure P

module Along {C D : CAT} (F : MAP C D) (x y : Obj-abs C)
  {a : MAP One (C × C)} {e : MAP One (D × D)}
  (θ : a =₁ pair x y) (κ : e =₁ pair (F ∘ x) (F ∘ y))
  (δ : (productMap F F ∘ a) =₁ e)
  (triangle : (productMap-pair F F x y ∙ (productMap F F ◁ θ)) =₂ (κ ∙ δ)) where
  private
    module Paired = Squares.Pair 𝒯 (funPost {C = [1]} F) F F ev₀ ev₁ ev₀ ev₁
      ((evaluate-post zero F) ⁻¹) ((evaluate-post one F) ⁻¹) using (matching)
    module Square = Changes.Along 𝒯 P endpoints (funPost F) endpoints (productMap F F)
      Paired.matching θ κ δ (productMap-pair F F x y) triangle
      using (source-change; target-change; image-before; image-after; prescribed)
    module Source = Families.ChangeFamily 𝒯 M ℱ P I θ using (map; map-isEquiv)
    module Target = Families.ChangeFamily 𝒯 M ℱ P I κ using (map; map-isEquiv)
    module HomImage = HomImages.At 𝒯 M ℱ P I F x y using (prescribed)

  source-change : MAP (Pullback endpoints a) (Hom C x y)
  source-change = Source.map
  target-change : MAP (Pullback endpoints e) (Hom D (F ∘ x) (F ∘ y))
  target-change = Target.map
  source-change-isEquiv = Source.map-isEquiv
  target-change-isEquiv = Target.map-isEquiv
  image-map : MAP (Pullback endpoints a) (Pullback endpoints e)
  image-map = Square.image-before
  private
    target-cone = pullbackCone endpoints (pair (F ∘ x) (F ∘ y))

  prescribed : ConeIso (conePre (target-change ∘ image-map) target-cone)
    (conePre (hom-post F x y ∘ source-change) target-cone)
  prescribed = coneIso-compose
    (conePre-assoc source-change (hom-post F x y) target-cone)
    (coneIso-compose (coneIso-pre source-change HomImage.prescribed)
      (coneIso-compose (coneIso-inverse (conePre-assoc source-change Square.image-after target-cone))
        Square.prescribed))
  private
    module Lifted = Lifting.Lift 𝒯 P (target-change ∘ image-map) (hom-post F x y ∘ source-change) prescribed
      using (lift; comparison-image; left-image; right-image)
  open Lifted public using (comparison-image; left-image; right-image) renaming (lift to comparison)
```


The target endpoints can themselves be changed by a specified
identification of their pair. This retains the endpoint transport after
hom-post, as required by the right side of a hom pullback.

```agda
module Framed {C D : CAT} (F : MAP C D) (x y : Obj-abs C) (x′ y′ : Obj-abs D)
  (ψ : pair (F ∘ x) (F ∘ y) =₁ pair x′ y′)
  {a : MAP One (C × C)} {e : MAP One (D × D)}
  (θ : a =₁ pair x y) (κ : e =₁ pair x′ y′)
  (δ : (productMap F F ∘ a) =₁ e)
  (triangle : ((ψ ∙ productMap-pair F F x y) ∙ (productMap F F ◁ θ)) =₂ (κ ∙ δ)) where
  private
    module Paired = Squares.Pair 𝒯 (funPost {C = [1]} F) F F ev₀ ev₁ ev₀ ev₁
      ((evaluate-post zero F) ⁻¹) ((evaluate-post one F) ⁻¹) using (matching)
    module Square = Changes.Along 𝒯 P endpoints (funPost F) endpoints (productMap F F)
      Paired.matching θ κ δ (ψ ∙ productMap-pair F F x y) triangle
      using (image-before; image-after; prescribed)
    module Source = Families.ChangeFamily 𝒯 M ℱ P I θ using (map)
    module Target = Families.ChangeFamily 𝒯 M ℱ P I κ using (map)
    module Transport = Families.ChangeFamily 𝒯 M ℱ P I ψ using (map; map-isEquiv)
    module TargetImage = Changes.TargetChange 𝒯 P endpoints (pair x y) (funPost F)
      endpoints (productMap F F) Paired.matching (productMap-pair F F x y) ψ
      using (comparison; comparison-image)
    module HomImage = HomImages.At 𝒯 M ℱ P I F x y using (comparison; comparison-image)

  source-change = Source.map
  target-change = Target.map
  endpoint-transport : MAP (Hom D (F ∘ x) (F ∘ y)) (Hom D x′ y′)
  endpoint-transport = Transport.map
  endpoint-transport-isEquiv = Transport.map-isEquiv
  post-map : MAP (Hom C x y) (Hom D x′ y′)
  post-map = endpoint-transport ∘ hom-post F x y
  image-map = Square.image-before

  image-normalization : Square.image-after =₁ post-map
  image-normalization = (endpoint-transport ◁ HomImage.comparison) ∙ (TargetImage.comparison) ⁻¹
  open TargetImage public using () renaming (comparison-image to target-image-computation)
  open HomImage public using () renaming (comparison-image to hom-image-computation)
  private
    target-cone = pullbackCone endpoints (pair x′ y′)
  prescribed : ConeIso (conePre (target-change ∘ image-map) target-cone)
    (conePre (post-map ∘ source-change) target-cone)
  prescribed = coneIso-compose (cone-action target-cone (image-normalization ▷ source-change)) Square.prescribed
  private
    module Lifted = Lifting.Lift 𝒯 P (target-change ∘ image-map) (post-map ∘ source-change) prescribed
      using (lift; comparison-image; left-image; right-image)
  open Lifted public using (comparison-image; left-image; right-image) renaming (lift to comparison)
```
