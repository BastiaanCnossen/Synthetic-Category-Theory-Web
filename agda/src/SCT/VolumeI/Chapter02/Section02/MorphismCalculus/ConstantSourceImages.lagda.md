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
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilies 𝒯 M ℱ I
  using (FamilyOperation; constant-family; variable-family; represented;
    post-operation; transport; compose-operations; constant-image-frame; post-variable-frame)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)

image : {Γ C D : CAT} (F : MAP C D) {x : Obj-abs C} {q : MAP Γ C} →
  MorphismExpression (const x) q → MorphismExpression (const (F ∘ x)) (F ∘ q)
image {Γ} F {x} {q} f = retarget-expression (post-expression F f)
  (constant-image Γ F x) (idIso (F ∘ q))

image-operation : {C D : CAT} (F : MAP C D) (x : Obj-abs C) →
  FamilyOperation (constant-family x) (variable-family C)
    (constant-family (F ∘ x)) (represented F)
image-operation {C} F x = compose-operations
  (transport (constant-image-frame F x) (post-variable-frame F))
  (post-operation F (constant-family x) (variable-family C))
```

The constant endpoint is transported by `constant-image`; the variable
endpoint retains its identity frame. Their two comparisons supply restriction
and change of target for the whole operation.

```agda
module Restrict {Γ Δ C D : CAT} (F : MAP C D) {x : Obj-abs C} {q : MAP Γ C}
  (f : MorphismExpression (const x) q) (r : MAP Δ Γ) where
  abstract
    comparison : ExpressionIso
      (retarget-expression (restrict-expression (image F f) r)
        (const-pre (F ∘ x) r) (comp-assoc r q F))
      (image F (restrict f r))
    comparison = FamilyOperation.on-restriction (image-operation F x) q f r

module Change {Γ C D : CAT} (F : MAP C D) {x : Obj-abs C} {q t : MAP Γ C}
  (f : MorphismExpression (const x) q) (g : MorphismExpression (const x) t)
  (σ : q =₁ t) (Φ : ExpressionIso (retarget-expression f (idIso (const x)) σ) g) where
  abstract
    comparison : ExpressionIso
      (retarget-expression (image F f) (idIso (const (F ∘ x))) (F ◁ σ)) (image F g)
    comparison = expressionIso-compose
      (FamilyOperation.on-comparison (image-operation F x) t Φ)
      (FamilyOperation.on-change (image-operation F x) f σ)
```
