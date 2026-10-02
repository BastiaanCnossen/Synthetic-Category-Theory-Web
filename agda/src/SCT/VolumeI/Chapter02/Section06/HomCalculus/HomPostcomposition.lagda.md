# Functorial images in hom categories

The existing hom functor sends a framed family of morphisms to its
postcomposed family, with constant endpoints normalized by associativity.
The comparison commutes with restriction and retains both endpoint equations.
Its restriction law is assembled by composing postcomposition with endpoint
transport along constant-image, using the shared endpoint-family constructors.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomRestriction 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilies 𝒯 M ℱ I
  using (FamilyOperation; constant-family; post; constant-image-frame; transport; compose-operations; post-operation)

open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M
  using (constant-image)

hom-image : {Γ C D : CAT} (F : MAP C D) {x y : Obj-abs C} →
  MorphismExpression (const {P = Γ} x) (const y) →
  MorphismExpression (const (F ∘ x)) (const (F ∘ y))
hom-image {Γ} F {x} {y} α = retarget-expression (post-expression F α)
  (constant-image Γ F x) (constant-image Γ F y)

hom-image-cong : {Γ C D : CAT} (F : MAP C D) {x y : Obj-abs C}
  {α β : MorphismExpression (const {P = Γ} x) (const y)} →
  ExpressionIso α β → ExpressionIso (hom-image F α) (hom-image F β)
hom-image-cong {Γ} F {x} {y} Φ = retarget-expressionIso (post-expressionIso F Φ)
  (constant-image Γ F x) (constant-image Γ F y)

hom-image-operation : {C D : CAT} (F : MAP C D) (x y : Obj-abs C) →
  FamilyOperation (constant-family {B = One} x) (constant-family y)
    (constant-family (F ∘ x)) (constant-family (F ∘ y))
hom-image-operation F x y = compose-operations
  {u = constant-family x} {v = constant-family y}
  {s = post F (constant-family x)} {t = post F (constant-family y)}
  {x = constant-family (F ∘ x)} {y = constant-family (F ∘ y)}
  (transport {u = post F (constant-family x)} {v = post F (constant-family y)}
    {s = constant-family (F ∘ x)} {t = constant-family (F ∘ y)}
    (constant-image-frame F x) (constant-image-frame F y))
  (post-operation F (constant-family x) (constant-family y))

module Restrict {Γ Δ C D : CAT} (F : MAP C D) {x y : Obj-abs C}
  (α : MorphismExpression (const {P = Γ} x) (const y)) (r : MAP Δ Γ) where
  comparison : ExpressionIso (hom-restrict (hom-image F α) r)
    (hom-image F (hom-restrict α r))
  comparison = FamilyOperation.on-restriction (hom-image-operation F x y) (terminate Γ) α r

hom-image-restrict : {Γ Δ C D : CAT} (F : MAP C D) {x y : Obj-abs C}
  (α : MorphismExpression (const {P = Γ} x) (const y)) (r : MAP Δ Γ) →
  ExpressionIso (hom-restrict (hom-image F α) r) (hom-image F (hom-restrict α r))
hom-image-restrict = Restrict.comparison

hom-post-β : {Γ C D : CAT} (F : MAP C D) (x y : Obj-abs C)
  (h : MAP Γ (Hom C x y)) →
  ExpressionIso (hom-expression (hom-post F x y ∘ h)) (hom-image F (hom-expression h))
hom-post-β F x y h = expressionIso-compose
  (hom-image-cong F (expressionIso-compose (hom-expression-cong (comp-unitˡ h))
    (expressionIso-inverse (hom-expression-restrict (id _) h))))
  (expressionIso-compose (hom-image-restrict F (hom-expression (id _)) h)
    (expressionIso-compose (hom-restrict-cong (hom-β (hom-image F (hom-expression (id _)))) h)
      (hom-expression-restrict (hom-post F x y) h)))
```

The same rule at the identity parameter computes the functor itself
without asking clients to unfold its defining pullback lift.

```agda
abstract
  hom-post-computation : {C D : CAT} (F : MAP C D) (x y : Obj-abs C) →
    ExpressionIso (hom-expression (hom-post F x y))
      (hom-image F (hom-expression (id (Hom C x y))))
  hom-post-computation F x y = expressionIso-compose (hom-post-β F x y (id _))
    (hom-expression-cong ((comp-unitʳ (hom-post F x y)) ⁻¹))
```
