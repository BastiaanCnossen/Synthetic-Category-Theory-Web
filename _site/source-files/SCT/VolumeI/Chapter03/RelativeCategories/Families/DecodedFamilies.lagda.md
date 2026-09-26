# Decoding a comparison of evaluated families

An identification between two universal evaluations can be evaluated
at an absolute point. The formula below keeps the terminal-product
insertion explicit. It is used to compute the underlying functors of
operations on relative mapping points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter03.RelativeCategories.Families.DecodedFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ

at-point : {X C D E : CAT} (l : MAP X (Fun C E)) (r : MAP X (Fun C D))
  (k : MAP D E) → funUncurry l =₁ (k ∘ funUncurry r) →
  (x : Obj-abs X) → decodeFun (l ∘ x) =₁ (k ∘ decodeFun (r ∘ x))
at-point {C = C} l r k α x = comp-assoc (oneProduct-in C) (funUncurry (r ∘ x)) k ∙
  (((k ◁ (funUncurry-restrict r x) ⁻¹) ▷ oneProduct-in C) ∙
    ((comp-assoc (productMap x (id C)) (funUncurry r) k ▷ oneProduct-in C) ∙
      (((α ▷ productMap x (id C)) ▷ oneProduct-in C) ∙
        (funUncurry-restrict l x ▷ oneProduct-in C))))

family-at-point : {X C D : CAT} (l : MAP X (Fun C D)) (x : Obj-abs X) →
  decodeFun (l ∘ x) =₁ (funUncurry l ∘ (productMap x (id C) ∘ oneProduct-in C))
family-at-point {C = C} l x = comp-assoc (oneProduct-in C) (productMap x (id C)) (funUncurry l) ∙
  (funUncurry-restrict l x ▷ oneProduct-in C)
```
