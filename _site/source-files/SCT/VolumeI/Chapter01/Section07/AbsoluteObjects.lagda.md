# Functors as absolute objects of the functor category

The remark following `def:Currying` uses the equivalence between `One × C`
and `C`. Naming curries the functor composed with the second projection;
decoding evaluates after inserting the terminal coordinate. Both inverse
comparisons are derived. The name `Obj-abs` keeps its established meaning.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.AbsoluteObjects
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using
  (oneProduct-in; oneProduct-section; oneProduct-retraction)
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ

nameFun : {C D : CAT} → MAP C D → Obj-abs (Fun C D)
nameFun f = funCurry (f ∘ pr₂)

decodeFun : {C D : CAT} → Obj-abs (Fun C D) → MAP C D
decodeFun {C} a = funUncurry a ∘ oneProduct-in C

decode-nameFun : {C D : CAT} (f : MAP C D) → (decodeFun (nameFun f)) =₁ f
decode-nameFun {C} f = comp-unitʳ f ∙
  ((f ◁ oneProduct-retraction C) ∙
    (comp-assoc (oneProduct-in C) pr₂ f ∙
      (funCurry-β (f ∘ pr₂) ▷ oneProduct-in C)))

name-decodeFun : {C D : CAT} (a : Obj-abs (Fun C D)) → (nameFun (decodeFun a)) =₁ a
name-decodeFun {C} a = funReflect _ a
  (comp-unitʳ (funUncurry a) ∙
    ((funUncurry a ◁ oneProduct-section C) ∙
      (comp-assoc pr₂ (oneProduct-in C) (funUncurry a) ∙
        funCurry-β (decodeFun a ∘ pr₂))))

```
