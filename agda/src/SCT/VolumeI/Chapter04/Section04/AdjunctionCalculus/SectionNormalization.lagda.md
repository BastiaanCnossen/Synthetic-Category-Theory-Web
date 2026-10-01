# Restricting normalized transformations to a section

An identity comparison over the base restricts to an identity comparison
after evaluation on the section. The compatibility uses the actual
section frames, including their associators and unitors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I
  using (restrict-post)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SectionFrames as Frames

private
  cancel-tail : {X Y : CAT} {u v w : MAP X Y}
    (α : u =₁ w) (β : u =₁ v) → ((α ∙ β ⁻¹) ∙ β) =₂ α
  cancel-tail α β = isoComp-unitʳ-at α ∙
    (isoComp-cong (idIso α) (isoComp-inverseˡ-at β) ∙ isoComp-assoc-at α (β ⁻¹) β)

module Transfer {C D : CAT} (p : MAP C D) (s : MAP D C)
  {x y : MAP C C} (f : MorphismExpression x y)
  (α : (x ∘ s) =₁ s) (β : (y ∘ s) =₁ s)
  (u : (p ∘ x) =₁ p) (v : (p ∘ y) =₁ p)
  (source : (p ◁ α) =₂ ((u ▷ s) ∙ (comp-assoc s x p) ⁻¹))
  (target : (p ◁ β) =₂ ((v ▷ s) ∙ (comp-assoc s y p) ⁻¹)) where
  on-section = retarget-expression (restrict-expression f s) α β
  over-base = retarget-expression (post-expression p f) u v

  abstract
    comparison : ExpressionIso (post-expression p on-section) (restrict-expression over-base s)
    comparison = expressionIso-compose (expressionIso-inverse (restrict-retarget (post-expression p f) u v s))
      (expressionIso-compose
        (retarget-cong (restrict-expression (post-expression p f) s)
          (cancel-tail (u ▷ s) (comp-assoc s x p) ∙ isoComp-cong source (idIso (comp-assoc s x p)))
          (cancel-tail (v ▷ s) (comp-assoc s y p) ∙ isoComp-cong target (idIso (comp-assoc s y p))))
        (expressionIso-compose
          (retarget-assoc (restrict-expression (post-expression p f) s)
            (comp-assoc s x p) (comp-assoc s y p) (p ◁ α) (p ◁ β))
          (expressionIso-compose
            (retarget-expressionIso (expressionIso-inverse (restrict-post p f s)) (p ◁ α) (p ◁ β))
            (post-retarget p (restrict-expression f s) α β))))

    identity : ExpressionIso over-base (identity-expression p) →
      ExpressionIso (post-expression p on-section) (identity-expression (p ∘ s))
    identity normal = expressionIso-compose (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E p s)
      (expressionIso-compose (restrict-expressionIso normal s) comparison)

module WithSection {C D : CAT} (p : MAP C D) (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
  module F = Frames.WithSection 𝒯 p s ρ
  module Right (η : MorphismExpression (id C) (s ∘ p)) = Transfer p s η
    (comp-unitˡ s) F.section-frame (comp-unitʳ p) F.vertical-frame
    F.identity-frame F.section-frame-image
  module Left (ε : MorphismExpression (s ∘ p) (id C)) = Transfer p s ε
    F.section-frame (comp-unitˡ s) F.vertical-frame (comp-unitʳ p)
    F.section-frame-image F.identity-frame
```
