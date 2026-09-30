# Images of families with constant source

A functor sends a family with constant source to another such family.
The comparisons below retain the target identification under restriction
and under a change of target. They specialize both to coslices and to
hom families.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceImages
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction 𝒯 M ℱ I public using (restrict)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; post-retarget; restrict-retarget-outer)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I using (restrict-post)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image; constant-image-pre)

image : {Γ C D : CAT} (F : MAP C D) {x : Obj-abs C} {q : MAP Γ C} →
  MorphismExpression (const x) q → MorphismExpression (const (F ∘ x)) (F ∘ q)
image {Γ} F {x} {q} f = retarget-expression (post-expression F f)
  (constant-image Γ F x) (idIso (F ∘ q))

module Restrict {Γ Δ C D : CAT} (F : MAP C D) {x : Obj-abs C} {q : MAP Γ C}
  (f : MorphismExpression (const x) q) (r : MAP Δ Γ) where
  private
    raw = restrict-expression (post-expression F f) r
    cx = constant-image Δ F x
    px = F ◁ const-pre x r
    py = F ◁ idIso (q ∘ r)
    ax = comp-assoc r (const x) F
    ay = comp-assoc r q F
    source-id = idIso (const {P = Δ} (F ∘ x))
    target-id = idIso (F ∘ (q ∘ r))
    first = restrict-retarget-outer (post-expression F f)
      (constant-image Γ F x) (idIso (F ∘ q)) r
      (const-pre (F ∘ x) r) ay
    abstract
      source-normal : (const-pre (F ∘ x) r ∙ (constant-image Γ F x ▷ r)) =₂ ((cx ∙ px) ∙ ax)
      source-normal = (isoComp-assoc-at cx px ax) ⁻¹ ∙ constant-image-pre r F x
      target-normal : (ay ∙ (idIso (F ∘ q) ▷ r)) =₂ ((target-id ∙ py) ∙ ay)
      target-normal = (isoComp-unitˡ-at ay ∙
        isoComp-cong (postWhisker-idIso F (q ∘ r) ∙ isoComp-unitˡ-at py) (idIso ay)) ⁻¹ ∙
        isoComp-unitʳ-at ay ∙ isoComp-cong (idIso ay) (preWhisker-idIso (F ∘ q) r)
    normalize = retarget-cong raw source-normal target-normal
    split = expressionIso-inverse (retarget-assoc raw ax ay (cx ∙ px) (target-id ∙ py))
    commute = retarget-expressionIso (restrict-post F f r) (cx ∙ px) (target-id ∙ py)
    join = expressionIso-inverse
      (retarget-assoc (post-expression F (restrict-expression f r)) px py cx target-id)
    last = retarget-expressionIso (expressionIso-inverse
      (post-retarget F (restrict-expression f r) (const-pre x r) (idIso (q ∘ r)))) cx target-id

  abstract
    comparison : ExpressionIso
      (retarget-expression (restrict-expression (image F f) r) (const-pre (F ∘ x) r) ay)
      (image F (restrict f r))
    comparison = expressionIso-compose last (expressionIso-compose join
      (expressionIso-compose commute (expressionIso-compose split
        (expressionIso-compose normalize first))))

module Change {Γ C D : CAT} (F : MAP C D) {x : Obj-abs C} {q t : MAP Γ C}
  (f : MorphismExpression (const x) q) (g : MorphismExpression (const x) t)
  (σ : q =₁ t) (Φ : ExpressionIso (retarget-expression f (idIso (const x)) σ) g) where
  private
    raw = post-expression F f
    cx = constant-image Γ F x
    sx = idIso (const {P = Γ} (F ∘ x))
    px = F ◁ idIso (const {P = Γ} x)
    py = F ◁ σ
    ty = idIso (F ∘ t)
    abstract
      source-normal : (sx ∙ cx) =₂ (cx ∙ px)
      source-normal = (isoComp-unitʳ-at cx ∙ isoComp-cong (idIso cx)
        (postWhisker-idIso F (const {P = Γ} x))) ⁻¹ ∙ isoComp-unitˡ-at cx
      target-normal : (py ∙ idIso (F ∘ q)) =₂ (ty ∙ py)
      target-normal = (isoComp-unitˡ-at py) ⁻¹ ∙ isoComp-unitʳ-at py

  abstract
    comparison : ExpressionIso (retarget-expression (image F f) sx py) (image F g)
    comparison = expressionIso-compose (retarget-expressionIso (post-expressionIso F Φ) cx ty)
      (expressionIso-compose (retarget-expressionIso (expressionIso-inverse
        (post-retarget F f (idIso (const x)) σ)) cx ty)
      (expressionIso-compose (expressionIso-inverse (retarget-assoc raw px py cx ty))
      (expressionIso-compose (retarget-cong raw source-normal target-normal)
        (retarget-assoc raw cx (idIso (F ∘ q)) sx py))))
```
