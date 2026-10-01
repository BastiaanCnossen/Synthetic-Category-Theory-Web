# Transposition over a fixed base

For functors from a base category into the two sides of an adjunction,
these formulas transpose arrows in the corresponding endpoint pullbacks.
The associators convert between composite endpoint functors and component
expressions. Comparisons of base functors preserve the specified frames.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameSquares 𝒯 M ℱ I using (retarget-square)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)

module Families {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module A = Adjunction adj
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj
      using (transpose-cong; untranspose-cong; transpose-retarget; untranspose-retarget)

  left-normal : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression ((l ∘ x) ∘ b) (y ∘ b) → MorphismExpression (l ∘ (x ∘ b)) (y ∘ b)
  left-normal b f = retarget-expression f (comp-assoc b x l) (idIso (y ∘ b))

  right-normal : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression (x ∘ b) ((r ∘ y) ∘ b) → MorphismExpression (x ∘ b) (r ∘ (y ∘ b))
  right-normal b f = retarget-expression f (idIso (x ∘ b)) (comp-assoc b y r)

  forward : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression ((l ∘ x) ∘ b) (y ∘ b) → MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)
  forward b f = retarget-expression (A.transpose (x ∘ b) (y ∘ b) (left-normal b f))
    (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹)

  backward : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression (x ∘ b) ((r ∘ y) ∘ b) → MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)
  backward b f = retarget-expression (A.untranspose (x ∘ b) (y ∘ b) (right-normal b f))
    ((comp-assoc b x l) ⁻¹) (idIso (y ∘ b))

  abstract
    forward-cong : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)} → ExpressionIso f g →
      ExpressionIso (forward b f) (forward b g)
    forward-cong b Φ = retarget-expressionIso
      (N.transpose-cong (x ∘ b) (y ∘ b) (retarget-expressionIso Φ (comp-assoc b x l) (idIso (y ∘ b))))
      (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹)

    backward-cong : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)} → ExpressionIso f g →
      ExpressionIso (backward b f) (backward b g)
    backward-cong b Φ = retarget-expressionIso
      (N.untranspose-cong (x ∘ b) (y ∘ b) (retarget-expressionIso Φ (idIso (x ∘ b)) (comp-assoc b y r)))
      ((comp-assoc b x l) ⁻¹) (idIso (y ∘ b))

    left-normal-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (left-normal b f) (l ◁ (x ◁ σ)) (y ◁ σ))
        (left-normal d (retarget-expression f ((l ∘ x) ◁ σ) (y ◁ σ)))
    left-normal-change {b = b} {d} f σ = retarget-square f
      (comp-assoc b x l) (idIso (y ∘ b)) ((l ∘ x) ◁ σ) (y ◁ σ)
      (l ◁ (x ◁ σ)) (y ◁ σ) (comp-assoc d x l) (idIso (y ∘ d))
      ((postWhisker-comp-at σ x l) ⁻¹)
      ((isoComp-unitˡ-at (y ◁ σ)) ⁻¹ ∙ isoComp-unitʳ-at (y ◁ σ))

    right-normal-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (right-normal b f) (x ◁ σ) (r ◁ (y ◁ σ)))
        (right-normal d (retarget-expression f (x ◁ σ) ((r ∘ y) ◁ σ)))
    right-normal-change {b = b} {d} f σ = retarget-square f
      (idIso (x ∘ b)) (comp-assoc b y r) (x ◁ σ) ((r ∘ y) ◁ σ)
      (x ◁ σ) (r ◁ (y ◁ σ)) (idIso (x ∘ d)) (comp-assoc d y r)
      ((isoComp-unitˡ-at (x ◁ σ)) ⁻¹ ∙ isoComp-unitʳ-at (x ◁ σ))
      ((postWhisker-comp-at σ y r) ⁻¹)

    forward-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (forward b f) (x ◁ σ) ((r ∘ y) ◁ σ))
        (forward d (retarget-expression f ((l ∘ x) ◁ σ) (y ◁ σ)))
    forward-change {b = b} {d} f σ = expressionIso-compose
      (retarget-expressionIso
        (expressionIso-compose (N.transpose-cong (x ∘ d) (y ∘ d) (left-normal-change f σ))
          (N.transpose-retarget (left-normal b f) (x ◁ σ) (y ◁ σ)))
        (idIso (x ∘ d)) ((comp-assoc d y r) ⁻¹))
      (retarget-square (A.transpose (x ∘ b) (y ∘ b) (left-normal b f))
        (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹) (x ◁ σ) (r ◁ (y ◁ σ))
        (x ◁ σ) ((r ∘ y) ◁ σ) (idIso (x ∘ d)) ((comp-assoc d y r) ⁻¹)
        ((isoComp-unitˡ-at (x ◁ σ)) ⁻¹ ∙ isoComp-unitʳ-at (x ◁ σ))
        ((move-square (comp-assoc d y r) ((r ∘ y) ◁ σ) (r ◁ (y ◁ σ))
          (comp-assoc b y r) (postWhisker-comp-at σ y r)) ⁻¹))

    backward-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (backward b f) ((l ∘ x) ◁ σ) (y ◁ σ))
        (backward d (retarget-expression f (x ◁ σ) ((r ∘ y) ◁ σ)))
    backward-change {b = b} {d} f σ = expressionIso-compose
      (retarget-expressionIso
        (expressionIso-compose (N.untranspose-cong (x ∘ d) (y ∘ d) (right-normal-change f σ))
          (N.untranspose-retarget (right-normal b f) (x ◁ σ) (y ◁ σ)))
        ((comp-assoc d x l) ⁻¹) (idIso (y ∘ d)))
      (retarget-square (A.untranspose (x ∘ b) (y ∘ b) (right-normal b f))
        ((comp-assoc b x l) ⁻¹) (idIso (y ∘ b)) (l ◁ (x ◁ σ)) (y ◁ σ)
        ((l ∘ x) ◁ σ) (y ◁ σ) ((comp-assoc d x l) ⁻¹) (idIso (y ∘ d))
        ((move-square (comp-assoc d x l) ((l ∘ x) ◁ σ) (l ◁ (x ◁ σ))
          (comp-assoc b x l) (postWhisker-comp-at σ x l)) ⁻¹)
        ((isoComp-unitˡ-at (y ◁ σ)) ⁻¹ ∙ isoComp-unitʳ-at (y ◁ σ)))
```
