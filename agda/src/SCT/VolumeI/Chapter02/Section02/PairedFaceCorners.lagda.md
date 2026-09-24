# Pairing the vertex equations of two faces

The endpoint equations for two scalar coordinates assemble into the
corner equation for their product. The edge comparisons remain the
specified pairings of their scalar frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section02.PairedProjectionComposition as Paired
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as Projection
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.PairedFaceCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
module PS = Projection 𝒯

module At {X A B K L : CAT} (F : MAP X A) (G : MAP X B)
  (d : MAP K X) (k : MAP L X) (u : Obj-abs K) (v : Obj-abs L)
  {F₀ : MAP K A} {G₀ : MAP K B} {F₁ : MAP L A} {G₁ : MAP L B}
  {x : Obj-abs A} {y : Obj-abs B}
  (fd : (F ∘ d) =₁ F₀) (gd : (G ∘ d) =₁ G₀)
  (fk : (F ∘ k) =₁ F₁) (gk : (G ∘ k) =₁ G₁)
  (fu : (F₀ ∘ u) =₁ x) (gu : (G₀ ∘ u) =₁ y)
  (fv : (F₁ ∘ v) =₁ x) (gv : (G₁ ∘ v) =₁ y)
  (δ : (d ∘ u) =₁ (k ∘ v)) where
  module Source = Paired.At 𝒯 M ℱ F G d u fd gd fu gu
  module Target = Paired.At 𝒯 M ℱ F G k v fk gk fv gv
  first-before = (fu ∙ (fd ▷ u)) ∙ (comp-assoc u d F) ⁻¹
  first-after = (fv ∙ (fk ▷ v)) ∙ (comp-assoc v k F) ⁻¹
  second-before = (gu ∙ (gd ▷ u)) ∙ (comp-assoc u d G) ⁻¹
  second-after = (gv ∙ (gk ▷ v)) ∙ (comp-assoc v k G) ⁻¹
  left-boundary = (Source.first ▷ u) ∙ (comp-assoc u d (pair F G)) ⁻¹
  right-boundary = (Target.first ▷ v) ∙ (comp-assoc v k (pair F G)) ⁻¹
  point-corner = Target.second ⁻¹ ∙ Source.second

  abstract
    framed : (first-after ∙ (F ◁ δ)) =₂ first-before →
      (second-after ∙ (G ◁ δ)) =₂ second-before →
      (Target.composite ∙ (pair F G ◁ δ)) =₂ Source.composite
    framed first second = Source.comparison ∙
      (Paired.paired-square 𝒯 M ℱ F G Source.left Target.left Source.right Target.right δ
        (isoComp-assoc-at fu (fd ▷ u) ((comp-assoc u d F) ⁻¹) ∙
          first ∙ isoComp-cong ((isoComp-assoc-at fv (fk ▷ v) ((comp-assoc v k F) ⁻¹)) ⁻¹) (idIso (F ◁ δ)))
        (isoComp-assoc-at gu (gd ▷ u) ((comp-assoc u d G) ⁻¹) ∙
          second ∙ isoComp-cong ((isoComp-assoc-at gv (gk ▷ v) ((comp-assoc v k G) ⁻¹)) ⁻¹) (idIso (G ◁ δ))) ∙
        isoComp-cong (Target.comparison ⁻¹) (idIso (pair F G ◁ δ)))

    corner : (first-after ∙ (F ◁ δ)) =₂ first-before →
      (second-after ∙ (G ◁ δ)) =₂ second-before →
      (point-corner ∙ left-boundary) =₂
        (right-boundary ∙ (pair F G ◁ δ))
    corner first second = cancel-left Target.second (right-boundary ∙ (pair F G ◁ δ)) ∙
      isoComp-cong (idIso (Target.second ⁻¹))
        (isoComp-assoc-at Target.second right-boundary (pair F G ◁ δ) ∙ (framed first second) ⁻¹) ∙
      isoComp-assoc-at (Target.second ⁻¹) Source.second left-boundary
```
