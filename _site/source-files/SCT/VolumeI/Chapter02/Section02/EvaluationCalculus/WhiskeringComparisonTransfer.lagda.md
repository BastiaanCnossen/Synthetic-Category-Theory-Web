# Transferring a fixed-input action

A comparison between the composite functor `K ∘ J` and `L` transfers a
framed description of the `J` action to the actual `L` action. Its endpoint
frames combine the given object comparisons with the functor comparison.
The result is an `ExpressionIso`, retaining both endpoint equations.

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

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.WhiskeringComparisonTransfer
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting

module Transfer {A B C : CAT} (K : MAP B C) (J : MAP A B) (L : MAP A C) (η : (K ∘ J) =₁ L)
  {x x′ : Obj-abs A} {y y′ : Obj-abs B} {z z′ : Obj-abs C}
  (f : MorphismExpression x x′) (g : MorphismExpression y y′)
  (δ : (J ∘ x) =₁ y) (δ′ : (J ∘ x′) =₁ y′)
  (κ : (K ∘ y) =₁ z) (κ′ : (K ∘ y′) =₁ z′)
  (given : ExpressionIso (retarget-expression (post-expression J f) δ δ′) g) where
  private
    module Paste = Pasting.At 𝒯 M ℱ P I E J K L η f
  double : MorphismExpression (K ∘ (J ∘ x)) (K ∘ (J ∘ x′))
  double = post-expression K (post-expression J f)
  source-change : (K ∘ (J ∘ x)) =₁ z
  source-change = κ ∙ (K ◁ δ)
  target-change : (K ∘ (J ∘ x′)) =₁ z′
  target-change = κ′ ∙ (K ◁ δ′)
  source-frame : (L ∘ x) =₁ z
  source-frame = source-change ∙ Paste.source-change ⁻¹
  target-frame : (L ∘ x′) =₁ z′
  target-frame = target-change ∙ Paste.target-change ⁻¹
  action : MorphismExpression z z′
  action = retarget-expression (post-expression L f) source-frame target-frame
  original : MorphismExpression z z′
  original = retarget-expression (post-expression K g) κ κ′

  abstract
    first : ExpressionIso (retarget-expression double source-change target-change) original
    first = expressionIso-compose (retarget-expressionIso (post-expressionIso K given) κ κ′)
      (expressionIso-compose (retarget-expressionIso (expressionIso-inverse (post-retarget K (post-expression J f) δ δ′)) κ κ′)
        (expressionIso-inverse (retarget-assoc double (K ◁ δ) (K ◁ δ′) κ κ′)))
    second : ExpressionIso (retarget-expression double source-change target-change) action
    second = expressionIso-compose (retarget-expressionIso Paste.comparison source-frame target-frame)
      (expressionIso-compose (expressionIso-inverse (retarget-assoc double Paste.source-change Paste.target-change source-frame target-frame))
        (expressionIso-inverse (retarget-cong double (cancel-inverse-tail source-change Paste.source-change)
          (cancel-inverse-tail target-change Paste.target-change))))
    comparison : ExpressionIso original action
    comparison = expressionIso-compose second (expressionIso-inverse first)

```
