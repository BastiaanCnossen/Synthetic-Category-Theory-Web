# Endpoint frames of the pullback hom cone

The represented product family has its own matching and leg comparisons.
Their whole-cone compatibility removes these choices from the endpoint
identification. The resulting formula uses only the restricted original
product cone and the specified productMap-pair comparisons.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.PullbackEndpointFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  vocabulary terminal products productLaws composition vertical whiskering using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-right)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft; coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
import SCT.VolumeI.Chapter01.Section06.Cospans.FamilyChange as Changes
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences as EndpointChanges
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductConeFrames as ConeFrames
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter02.Section06.HomCalculus.PullbackHomMaps as Maps

private
  framed-inverse-square : {X Y : CAT} {a a′ b b′ x y : MAP X Y}
    (q : a =₁ b) (q′ : a′ =₁ b′) (u : a =₁ a′) (v : b =₁ b′)
    (A : a′ =₁ x) (B : b′ =₁ y) → (q′ ∙ u) =₂ (v ∙ q) →
    (((A ∙ u) ∙ q ⁻¹) ∙ (B ∙ v) ⁻¹) =₂ ((A ∙ q′ ⁻¹) ∙ B ⁻¹)
  framed-inverse-square q q′ u v A B square =
    isoComp-cong (cancel-right v (A ∙ q′ ⁻¹)) (idIso (B ⁻¹)) ∙
    ((isoComp-assoc-at ((A ∙ q′ ⁻¹) ∙ v) (v ⁻¹) (B ⁻¹)) ⁻¹ ∙
    (isoComp-cong ((isoComp-assoc-at A (q′ ⁻¹) v) ⁻¹) (idIso (v ⁻¹ ∙ B ⁻¹)) ∙
    (isoComp-cong (isoComp-cong (idIso A) ((move-square q′ u v q square) ⁻¹))
      (idIso (v ⁻¹ ∙ B ⁻¹)) ∙
      isoComp-cong (isoComp-assoc-at A u (q ⁻¹)) (inverse-composite B v))))

module At {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) (es : IsPullback s) (x y : Obj-abs S) where
  private
    module HomMaps = Maps.At 𝒯 M ℱ P I s es x y
      using (p; q; matching; family-computation; endpoint-identification;
        left-family-identification; right-family-identification; base-family-identification;
        endpoint-transport; right-hom-map; hom-cone; hom-cone-isPullback)
    open HomMaps
    module Product = Products.Coordinates 𝒯 f f g g using (module Paired)
    F = productMap f f
    G = productMap g g
    L = ConeIso.leftIso family-computation
    R = ConeIso.rightIso family-computation

  product-cone = Product.Paired.cone (conePre pr₁ s) (conePre pr₂ s)
  restricted-cone = conePre (pair x y) product-cone
  left-frame = productMap-pair f f (p ∘ x) (p ∘ y) ∙ (F ◁ productMap-pair p p x y)
  right-frame = productMap-pair g g (q ∘ x) (q ∘ y) ∙ (G ◁ productMap-pair q q x y)
  original-endpoint-identification = (left-frame ∙ (Cone.match restricted-cone) ⁻¹) ∙ right-frame ⁻¹

  private
    left-normal : base-family-identification =₂ (left-frame ∙ (F ◁ L))
    left-normal = (isoComp-assoc-at (productMap-pair f f (p ∘ x) (p ∘ y))
      (F ◁ productMap-pair p p x y) (F ◁ L)) ⁻¹ ∙
      isoComp-cong (idIso (productMap-pair f f (p ∘ x) (p ∘ y)))
        (postWhisker-isoComp-at F (productMap-pair p p x y) L)
    right-normal : (productMap-pair g g (q ∘ x) (q ∘ y) ∙ (G ◁ right-family-identification)) =₂
      (right-frame ∙ (G ◁ R))
    right-normal = (isoComp-assoc-at (productMap-pair g g (q ∘ x) (q ∘ y))
      (G ◁ productMap-pair q q x y) (G ◁ R)) ⁻¹ ∙
      isoComp-cong (idIso (productMap-pair g g (q ∘ x) (q ∘ y)))
        (postWhisker-isoComp-at G (productMap-pair q q x y) R)

  endpoint-computation : endpoint-identification =₂ original-endpoint-identification
  endpoint-computation = framed-inverse-square matching (Cone.match restricted-cone)
    (F ◁ L) (G ◁ R) left-frame right-frame (ConeIso.compatible family-computation) ∙
    isoComp-cong (isoComp-cong left-normal (idIso (matching ⁻¹))) (＝-inv ◁ right-normal)


  endpoint-matching = pair-cong (Cone.match (conePre x s)) (Cone.match (conePre y s))

  private
    module Restricted = ConeFrames.Restricted 𝒯 s x y using (comparison)
    module Paired = ConeFrames.Paired 𝒯 (conePre x s) (conePre y s) using (matching-computation)
    source-frame = productMap f f ◁ productMap-pair p p x y
    target-frame = productMap g g ◁ productMap-pair q q x y
    left-pair = productMap-pair f f (p ∘ x) (p ∘ y)
    right-pair = productMap-pair g g (q ∘ x) (q ∘ y)
    paired-cone = Product.Paired.cone (conePre x s) (conePre y s)

  matching-computation : (right-frame ∙ Cone.match restricted-cone) =₂
    (endpoint-matching ∙ left-frame)
  matching-computation = isoComp-assoc-at endpoint-matching left-pair source-frame ∙
    (isoComp-cong Paired.matching-computation (idIso source-frame) ∙
    ((isoComp-assoc-at right-pair (Cone.match paired-cone) source-frame) ⁻¹ ∙
    (isoComp-cong (idIso right-pair) ((ConeIso.compatible Restricted.comparison) ⁻¹) ∙
      isoComp-assoc-at right-pair target-frame (Cone.match restricted-cone))))

  original-endpoint-computation : original-endpoint-identification =₂ (endpoint-matching ⁻¹)
  original-endpoint-computation = cancel-right right-frame (endpoint-matching ⁻¹) ∙
    isoComp-cong ((move-square endpoint-matching left-frame right-frame (Cone.match restricted-cone)
      (matching-computation ⁻¹)) ⁻¹) (idIso (right-frame ⁻¹))

  endpoint-pair-computation : endpoint-identification =₂ (endpoint-matching ⁻¹)
  endpoint-pair-computation = original-endpoint-computation ∙ endpoint-computation


  private
    module Normalized = EndpointChanges.ChangeFamily 𝒯 M ℱ P I (endpoint-matching ⁻¹)
      using (map; map-isEquiv)
    module EndpointComparison = Changes.Congruence 𝒯 P endpoints
      endpoint-identification (endpoint-matching ⁻¹) endpoint-pair-computation
      using (comparison; prescribed; comparison-image)

  normalized-endpoint-transport : MAP (Hom E (g ∘ (q ∘ x)) (g ∘ (q ∘ y)))
    (Hom E (f ∘ (p ∘ x)) (f ∘ (p ∘ y)))
  normalized-endpoint-transport = Normalized.map
  normalized-endpoint-transport-isEquiv = Normalized.map-isEquiv

  endpoint-transport-comparison : endpoint-transport =₁ normalized-endpoint-transport
  endpoint-transport-comparison = EndpointComparison.comparison
  open EndpointComparison public using () renaming (prescribed to endpoint-transport-prescribed;
    comparison-image to endpoint-transport-image)

  normalized-right-hom-map = normalized-endpoint-transport ∘ hom-post g (q ∘ x) (q ∘ y)
  right-hom-comparison : right-hom-map =₁ normalized-right-hom-map
  right-hom-comparison = endpoint-transport-comparison ▷ hom-post g (q ∘ x) (q ∘ y)

  normalized-hom-cone : Cone (hom-post f (p ∘ x) (p ∘ y)) normalized-right-hom-map (Hom S x y)
  normalized-hom-cone = coneSwap (changeLeft right-hom-comparison (coneSwap hom-cone))

  private
    module RightChange = ArrowChange.ChangeLeft 𝒯 P right-hom-comparison
      (hom-post f (p ∘ x) (p ∘ y)) using (preserve)
  normalized-hom-cone-isPullback : IsPullback normalized-hom-cone
  normalized-hom-cone-isPullback = pullback-swap _
    (RightChange.preserve (coneSwap hom-cone) (pullback-swap hom-cone hom-cone-isPullback))
```
