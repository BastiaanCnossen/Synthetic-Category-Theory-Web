# Uncurrying with changed endpoints

Uncurrying carries a change of endpoint frames to the corresponding
uncurried identifications. Restriction, pairing and evaluation each retain
their frame comparison; the last normalization uses the actual action of
uncurrying on isomorphisms.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget; retarget-id; post-retarget; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as Frames
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
open PC vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-Iso₂)

module At {Γ X C : CAT} {f g f′ g′ : MAP Γ (Fun X C)}
  (α : MorphismExpression f g) (p : f =₁ f′) (q : g =₁ g′) where
  fixed : MAP (Γ × X) X
  fixed = id X ∘ pr₂
  original = restrict-expression α (pr₁ {Γ} {X})
  constant = identity-expression fixed
  paired = pair-expression original constant
  first = p ▷ pr₁ {Γ} {X}
  last = q ▷ pr₁ {Γ} {X}
  source-change = pair-cong first (idIso fixed)
  target-change = pair-cong last (idIso fixed)
  module Product = Frames.At 𝒯 M ℱ I original constant first last (idIso fixed) (idIso fixed)
    using (value)

  frame-normalization : {a b : MAP Γ (Fun X C)} (r : a =₁ b) →
    funUncurryIso r =₂ (funEval ◁ pair-cong (r ▷ pr₁ {Γ} {X}) (idIso fixed))
  frame-normalization r = (postWhisker funEval ◁
      pair-cong-Iso₂ (idIso (r ▷ pr₁)) (preWhisker-idIso (id X) (pr₂ {Γ} {X}))) ∙ funUncurryIso-at r

  abstract
    pairing : ExpressionIso
      (pair-expression (restrict-expression (retarget-expression α p q) pr₁) constant)
      (retarget-expression paired source-change target-change)
    pairing = expressionIso-compose (expressionIso-inverse Product.value)
      (pair-expression-cong (restrict-retarget α p q pr₁) (expressionIso-inverse (retarget-id constant)))

    value : ExpressionIso (uncurry-expression (retarget-expression α p q))
      (retarget-expression (uncurry-expression α) (funUncurryIso p) (funUncurryIso q))
    value = expressionIso-compose
      (retarget-cong (uncurry-expression α) (frame-normalization p ⁻¹) (frame-normalization q ⁻¹))
      (expressionIso-compose (post-retarget funEval paired source-change target-change)
        (post-expressionIso funEval pairing))
```
