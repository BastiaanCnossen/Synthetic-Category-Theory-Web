# Evaluation reflects identifications between constant arrows

The identity-arrow functor is an embedding. Any retraction of it therefore
reflects identifications of identifications between constant-arrow
families. The proof lifts the two identifications with their specified
images and uses the naturality of the actual section frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationScalarReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding as Embedding
open Embedding.WithRezk 𝒯 M ℱ P I E S Q R using (identityArrow-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting 𝒯 P using (embedding-lift)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

module At {C : CAT} (p : MAP (Ar C) C) (ρ : (p ∘ identityArrow) =₁ id C) where
  module Images {Γ : CAT} {x y : MAP Γ C}
    (α β : (identityArrow ∘ x) =₁ (identityArrow ∘ y)) where
    private
      first-lift = embedding-lift identityArrow (identityArrow-isEmbedding C) x y α
      second-lift = embedding-lift identityArrow (identityArrow-isEmbedding C) x y β
      ai = FunctorLift.comparison first-lift
      bi = FunctorLift.comparison second-lift
      cx = constant-frame p ρ x
      cy = constant-frame p ρ y

    abstract
      first-image : (cy ∙ (p ◁ α)) =₂ (FunctorLift.lift first-lift ∙ cx)
      first-image = constant-frame-natural p ρ (FunctorLift.lift first-lift) ∙
        isoComp-cong (idIso cy) (postWhisker p ◁ ai ⁻¹)

      second-image : (cy ∙ (p ◁ β)) =₂ (FunctorLift.lift second-lift ∙ cx)
      second-image = constant-frame-natural p ρ (FunctorLift.lift second-lift) ∙
        isoComp-cong (idIso cy) (postWhisker p ◁ bi ⁻¹)

      reflect : (p ◁ α) =₂ (p ◁ β) → α =₂ β
      reflect same = bi ∙
        ((postWhisker identityArrow ◁ cancel-right-reflect cx
          (second-image ∙ (isoComp-cong (idIso cy) same ∙ first-image ⁻¹))) ∙ ai ⁻¹)

  module Framed {Γ : CAT} {x y : MAP Γ C} {h k : MAP Γ (Ar C)}
    (ξ : (identityArrow ∘ x) =₁ h) (ζ : (identityArrow ∘ y) =₁ k)
    (α β : h =₁ k) where
    left = ζ ⁻¹ ∙ (α ∙ ξ)
    right = ζ ⁻¹ ∙ (β ∙ ξ)

    abstract
      image-cong : (p ◁ α) =₂ (p ◁ β) → (p ◁ left) =₂ (p ◁ right)
      image-cong same = (postWhisker-isoComp-at p (ζ ⁻¹) (β ∙ ξ)) ⁻¹ ∙
        (isoComp-cong (idIso (p ◁ ζ ⁻¹))
          ((postWhisker-isoComp-at p β ξ) ⁻¹ ∙
            (isoComp-cong same (idIso (p ◁ ξ)) ∙ postWhisker-isoComp-at p α ξ)) ∙
          postWhisker-isoComp-at p (ζ ⁻¹) (α ∙ ξ))

      reflect : (p ◁ α) =₂ (p ◁ β) → α =₂ β
      reflect same = cancel-right-reflect ξ
        (cancel-left-reflect (ζ ⁻¹) (Images.reflect left right (image-cong same)))

  abstract
    section-reflect : (α β : identityArrow {C} =₁ identityArrow) →
      (p ◁ α) =₂ (p ◁ β) → α =₂ β
    section-reflect α β = Framed.reflect (comp-unitʳ identityArrow) (comp-unitʳ identityArrow) α β
```
