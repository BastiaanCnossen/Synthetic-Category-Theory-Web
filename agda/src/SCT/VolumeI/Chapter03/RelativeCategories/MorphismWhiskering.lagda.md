# Whiskering transformations over a base

Precomposition and postcomposition preserve the full comparison with the
identity transformation of the structure map. The proof keeps the
associators in the composite relative functors.

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

module SCT.VolumeI.Chapter03.RelativeCategories.MorphismWhiskering
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-retarget)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as Identity
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as Restriction

private
  abstract
    prefix-cancel : {Γ C : CAT} {x y z w : MAP Γ C}
      (α : y =₁ x) (β : y =₁ z) (γ : z =₁ w) →
      ((γ ∙ (β ∙ α ⁻¹)) ∙ α) =₂ (γ ∙ β)
    prefix-cancel α β γ = isoComp-cong (idIso γ)
        (isoComp-unitʳ-at β ∙ isoComp-cong (idIso β) (isoComp-inverseˡ-at α) ∙
          isoComp-assoc-at β (α ⁻¹) α) ∙
      isoComp-assoc-at γ (β ∙ α ⁻¹) α

module Pre {A C D B : CAT} {b : MAP A B} {p : MAP C B} {q : MAP D B}
  (t : FunctorOver b p) {u v : FunctorOver p q}
  (α : Over.MorphismOver p q u v) where
  private
    module T = FunctorLift t
    module U = FunctorLift u
    module V = FunctorLift v
    module F = Over.MorphismOver α
    module UT = FunctorLift (compose-over u t)
    module VT = FunctorLift (compose-over v t)

  abstract
    over-base : Over.IsOver b q (compose-over u t) (compose-over v t)
      (restrict-expression F.underlying T.lift)
    over-base = expressionIso-compose (Identity.At.comparison 𝒯 M ℱ P I E T.comparison)
      (expressionIso-compose
        (retarget-expressionIso (Restriction.Restrict.comparison 𝒯 M ℱ P I E p T.lift)
          T.comparison T.comparison)
        (expressionIso-compose
          (retarget-expressionIso (restrict-expressionIso F.over-base T.lift) T.comparison T.comparison)
          (expressionIso-inverse (restrict-post-retarget q F.underlying T.lift
            U.comparison V.comparison T.comparison T.comparison UT.comparison VT.comparison
            ((prefix-cancel (comp-assoc T.lift U.lift q) (U.comparison ▷ T.lift) T.comparison) ⁻¹)
            ((prefix-cancel (comp-assoc T.lift V.lift q) (V.comparison ▷ T.lift) T.comparison) ⁻¹)))))

  value : Over.MorphismOver b q (compose-over u t) (compose-over v t)
  value = record { underlying = restrict-expression F.underlying T.lift ; over-base = over-base }

module Post {C D E′ B : CAT} {p : MAP C B} {q : MAP D B} {b : MAP E′ B}
  (t : FunctorOver q b) {u v : FunctorOver p q}
  (α : Over.MorphismOver p q u v) where
  private
    module T = FunctorLift t
    module U = FunctorLift u
    module V = FunctorLift v
    module F = Over.MorphismOver α
    module Paste = Pasting.At 𝒯 M ℱ P I E T.lift b q T.comparison F.underlying

  abstract
    over-base : Over.IsOver p b (compose-over t u) (compose-over t v)
      (post-expression T.lift F.underlying)
    over-base = expressionIso-compose F.over-base
      (expressionIso-compose (retarget-expressionIso Paste.comparison U.comparison V.comparison)
        (expressionIso-inverse (retarget-assoc
          (post-expression b (post-expression T.lift F.underlying))
          Paste.source-change Paste.target-change U.comparison V.comparison)))

  value : Over.MorphismOver p b (compose-over t u) (compose-over t v)
  value = record { underlying = post-expression T.lift F.underlying ; over-base = over-base }
```
