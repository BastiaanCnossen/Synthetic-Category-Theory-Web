# Comparing points of a relative identification family

A family of identifications with a specified triangle can be evaluated
at any absolute point of its parameter. An identification of parameters
then gives a comparison of the resulting relative identifications,
including the compatibility one dimension higher. The proof uses the
naturality of evaluation and fixed-outer interchange.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.Families.IdentificationFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PointEvaluationNaturality 𝒯
  using (const-evaluate-natural; isoComp-evaluate-natural)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (transport-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P

module Family {A C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g)
  (α : MAP A (FunctorLift.lift u ＝ FunctorLift.lift v))
  (triangle : (const (FunctorLift.comparison v) ∙ (g ◁ α)) =₁
    const (FunctorLift.comparison u)) where
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  boundary = const θv ∙ (g ◁ α)

  normalization : (x : Obj-abs A) →
    (boundary ∘ x) =₁ (θv ∙ (g ◁ (α ∘ x)))
  normalization x = isoComp-evaluate (const θv) (g ◁ α) x
    (const-evaluate θv x) (comp-assoc x α (postWhisker g))

  at : Obj-abs A → FunctorOverIso u v
  at x = record { underlying = α ∘ x
    ; compatible = const-evaluate θu x ∙ ((triangle ▷ x) ∙ (normalization x) ⁻¹) }

  opaque
    normalization-natural : {x y : Obj-abs A} (δ : x =₁ y) →
      (normalization y ∙ (boundary ◁ δ)) =₂
      (isoComp-cong (idIso θv) (postWhisker g ◁ (α ◁ δ)) ∙ normalization x)
    normalization-natural {x} {y} δ = isoComp-evaluate-natural (const θv) (g ◁ α) δ
      (const-evaluate θv x) (const-evaluate θv y)
      (comp-assoc x α (postWhisker g)) (comp-assoc y α (postWhisker g))
      (idIso θv) (postWhisker g ◁ (α ◁ δ))
      (const-evaluate-natural θv δ) (postWhisker-comp-at δ α (postWhisker g))

  opaque
    naturality : {x y : Obj-abs A} (δ : x =₁ y) → FunctorOverIso₂ (at x) (at y)
    naturality {x} {y} δ = record { underlying = α ◁ δ
      ; compatible = isoComp-unitˡ-at (FunctorOverIso.compatible (at x)) ∙
          transport-square (normalization x) (normalization y)
            (const-evaluate θu x) (const-evaluate θu y)
            (triangle ▷ x) (triangle ▷ y) (boundary ◁ δ) (const θu ◁ δ)
            (isoComp-cong (idIso θv) (postWhisker g ◁ (α ◁ δ))) (idIso θu)
            (normalization-natural δ) (const-evaluate-natural θu δ) (interchange-at triangle δ) }
```
