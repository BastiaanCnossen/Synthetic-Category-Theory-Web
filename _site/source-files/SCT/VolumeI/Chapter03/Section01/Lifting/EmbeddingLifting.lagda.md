# Lifting a specified identification through an embedding

An embedding reflects an identification together with its specified
image. Factor the cone defined by that identification through the
universal diagonal. The quotient of its two leg comparisons is the
lifted identification; compatibility of the cone comparison gives its
image. This strengthens the earlier existence-only reflection lemma.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality

module SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding; diagonalCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Lift {A B Γ : CAT} (f : MAP A B) (ef : IsEmbedding f)
  (h k : MAP Γ A) (α : (f ∘ h) =₁ (f ∘ k)) where
  module U = UniversalCone (diagonalCone f) ef
  cone : Cone f f Γ
  cone = record { left = h ; right = k ; match = α }
  chosen = U.factor cone
  comparison = U.factor-β cone
  left = ConeIso.leftIso comparison
  right = ConeIso.rightIso comparison
  assoc = comp-assoc chosen (id A) f

  diagonal-matching : Cone.match (conePre chosen (diagonalCone f)) =₂ idIso (f ∘ (id A ∘ chosen))
  diagonal-matching = isoComp-inverseʳ-at assoc ∙
    isoComp-cong (idIso assoc)
      (isoComp-unitˡ-at (assoc ⁻¹) ∙
        isoComp-cong (preWhisker-idIso (f ∘ id A) chosen) (idIso (assoc ⁻¹)))

  square : (α ∙ (f ◁ left)) =₂ (f ◁ right)
  square = isoComp-unitʳ-at (f ◁ right) ∙
    (isoComp-cong (idIso (f ◁ right)) diagonal-matching ∙ ConeIso.compatible comparison)

  lift : h =₁ k
  lift = right ∙ left ⁻¹

  image : (f ◁ lift) =₂ α
  image = cancel-right (f ◁ left) α ∙
    (isoComp-cong (square ⁻¹) (idIso ((f ◁ left) ⁻¹)) ∙
      (isoComp-cong (idIso (f ◁ right)) (post-inverse f left) ∙
        postWhisker-isoComp-at f right (left ⁻¹)))

embedding-lift : {A B Γ : CAT} (f : MAP A B) → IsEmbedding f →
  (h k : MAP Γ A) (α : (f ∘ h) =₁ (f ∘ k)) → FunctorLift (postWhisker f) α
embedding-lift f ef h k α = record { lift = Lift.lift f ef h k α ; comparison = Lift.image f ef h k α }
```
