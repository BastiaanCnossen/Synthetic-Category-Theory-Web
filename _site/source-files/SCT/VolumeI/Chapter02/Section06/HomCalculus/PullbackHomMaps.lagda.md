# Hom maps of a pullback

The component maps in the fiber presentation become the literal hom-post
functor on the left and hom-post followed by specified endpoint transport
on the right. The endpoint transport retains the matching of the
represented product family. Its identification with the original square's
endpoint matching is a further computation.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.PullbackHomMaps
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  vocabulary terminal products productLaws composition vertical whiskering using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Transport
import SCT.VolumeI.Chapter02.Section06.HomCalculus.PullbackFamilies as Families
import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomFamilyPostcomposition as Images

module At {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) (es : IsPullback s) (x y : Obj-abs S) where
  open Families.At 𝒯 M ℱ P I s es x y public

  private
    module Left = Images.Along 𝒯 M ℱ P I f (p ∘ x) (p ∘ y)
      left-family-identification base-family-identification (idIso base-family)
      ((isoComp-unitʳ-at base-family-identification) ⁻¹)
      using (comparison; prescribed; comparison-image; left-image; right-image)

  left-comparison : (base-equivalence ∘ left-map) =₁
    (hom-post f (p ∘ x) (p ∘ y) ∘ left-equivalence)
  left-comparison = Left.comparison
  open Left public using () renaming (prescribed to left-prescribed;
    comparison-image to left-comparison-image; left-image to left-arrow-image; right-image to left-parameter-image)

  private
    right-pair = productMap-pair g g (q ∘ x) (q ∘ y)
    right-whisker = productMap g g ◁ right-family-identification
    right-frame = right-pair ∙ right-whisker
    matched-frame = base-family-identification ∙ matching ⁻¹

  endpoint-identification : pair (g ∘ (q ∘ x)) (g ∘ (q ∘ y)) =₁
    pair (f ∘ (p ∘ x)) (f ∘ (p ∘ y))
  endpoint-identification = matched-frame ∙ right-frame ⁻¹

  private
    triangle : ((endpoint-identification ∙ right-pair) ∙ right-whisker) =₂ matched-frame
    triangle = isoComp-unitʳ-at matched-frame ∙
      (isoComp-cong (idIso matched-frame) (isoComp-inverseˡ-at right-frame) ∙
      (isoComp-assoc-at matched-frame (right-frame ⁻¹) right-frame ∙
        isoComp-assoc-at endpoint-identification right-pair right-whisker))
    module Right = Images.Framed 𝒯 M ℱ P I g (q ∘ x) (q ∘ y)
      (f ∘ (p ∘ x)) (f ∘ (p ∘ y)) endpoint-identification
      right-family-identification base-family-identification (matching ⁻¹) triangle
      using (endpoint-transport; endpoint-transport-isEquiv; post-map;
        comparison; prescribed; comparison-image; left-image; right-image)

  open Right public using (endpoint-transport; endpoint-transport-isEquiv)
    renaming (post-map to right-hom-map)
  right-comparison : (base-equivalence ∘ right-map) =₁
    (right-hom-map ∘ right-equivalence)
  right-comparison = Right.comparison
  open Right public using () renaming (prescribed to right-prescribed;
    comparison-image to right-comparison-image; left-image to right-arrow-image; right-image to right-parameter-image)


  hom-cospan : CospanMap left-map right-map (hom-post f (p ∘ x) (p ∘ y)) right-hom-map
  hom-cospan = record
    { left = left-equivalence ; right = right-equivalence ; base = base-equivalence
    ; leftSquare = left-comparison ⁻¹ ; rightSquare = right-comparison ⁻¹ }

  hom-cone : Cone (hom-post f (p ∘ x) (p ∘ y)) right-hom-map (Hom S x y)
  hom-cone = CospanMap.mapCone hom-cospan fiber-cone

  private
    module Transported = Transport.Mapped 𝒯 P hom-cospan
      (degenerate-pullback base-equivalence-isEquiv (Transport.rightSquareOf 𝒯 P hom-cospan)
        right-equivalence-isEquiv) fiber-cone fiber-cone-isPullback using (isPullback)

  hom-cone-isPullback : IsPullback hom-cone
  hom-cone-isPullback = Transported.isPullback left-equivalence-isEquiv
```
