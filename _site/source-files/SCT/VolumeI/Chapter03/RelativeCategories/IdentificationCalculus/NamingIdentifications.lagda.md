# Naming identifications of functors

Naming a functor induces an equivalence on its animae of identifications.
We obtain the actual map by inverting decoding and changing its endpoints.
This lets relative constructions recover a specified triangle, including
its identification, from the corresponding point of a fiber.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in; oneProduct-in-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ
  using (post-nameFun; post-nameFun-uncurried; post-nameFun-image)
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv; left-evaluate; right-evaluate)

decodeFun-isoMap : {C D : CAT} (a b : Obj-abs (Fun C D))
  → MAP (a ＝ b) (decodeFun a ＝ decodeFun b)
decodeFun-isoMap {C} a b = preWhisker (oneProduct-in C) ∘ funUncurry-isoMap a b

decodeFun-isoMap-isEquiv : {C D : CAT} (a b : Obj-abs (Fun C D))
  → IsEquiv (decodeFun-isoMap a b)
decodeFun-isoMap-isEquiv {C} a b =
  equiv-compose (funUncurry-isoMap a b) (preWhisker (oneProduct-in C))
    (funUncurry-isoMap-isEquiv a b)
    (preWhisker-isEquiv (oneProduct-in C) (oneProduct-in-isEquiv C)
      (funUncurry a) (funUncurry b))

nameFun-isoMap : {C D : CAT} (f g : MAP C D) → MAP (f ＝ g) (nameFun f ＝ nameFun g)
nameFun-isoMap f g =
  IsEquiv.inverse (decodeFun-isoMap-isEquiv (nameFun f) (nameFun g)) ∘
    (leftMultiply ((decode-nameFun g) ⁻¹) ∘ rightMultiply (decode-nameFun f))

nameFun-isoMap-isEquiv : {C D : CAT} (f g : MAP C D) → IsEquiv (nameFun-isoMap f g)
nameFun-isoMap-isEquiv f g = equiv-compose
  (leftMultiply ((decode-nameFun g) ⁻¹) ∘ rightMultiply (decode-nameFun f))
  (IsEquiv.inverse (decodeFun-isoMap-isEquiv (nameFun f) (nameFun g)))
  (equiv-compose (rightMultiply (decode-nameFun f)) (leftMultiply ((decode-nameFun g) ⁻¹))
    (rightMultiply-isEquiv (decode-nameFun f)) (leftMultiply-isEquiv ((decode-nameFun g) ⁻¹)))
  (equiv-inverse (decodeFun-isoMap-isEquiv (nameFun f) (nameFun g)))

decodeFunIso : {C D : CAT} {x y : Obj-abs (Fun C D)} →
  x =₁ y → decodeFun x =₁ decodeFun y
decodeFunIso {x = x} {y} α = decodeFun-isoMap x y ∘ α

decodeFunIso-at : {C D : CAT} {x y : Obj-abs (Fun C D)} (α : x =₁ y) →
  decodeFunIso α =₂ (funUncurryIso α ▷ oneProduct-in C)
decodeFunIso-at {C} {x = x} {y} α =
  comp-assoc α (funUncurry-isoMap x y) (preWhisker (oneProduct-in C))

post-nameFun-decode-image : {B C D : CAT} (g : MAP C D) (f : MAP B C) →
  decodeFunIso (post-nameFun g f) =₂ (post-nameFun-uncurried g f ▷ oneProduct-in B)
post-nameFun-decode-image {B} g f =
  (preWhisker (oneProduct-in B) ◁ post-nameFun-image g f) ∙
    decodeFunIso-at (post-nameFun g f)

nameFunIso : {C D : CAT} {f g : MAP C D} → f =₁ g → nameFun f =₁ nameFun g
nameFunIso {f = f} {g} α = nameFun-isoMap f g ∘ α

module NamedIdentification {C D : CAT} (f g : MAP C D) (α : f =₁ g) where
  endpoints = leftMultiply ((decode-nameFun g) ⁻¹) ∘ rightMultiply (decode-nameFun f)
  prescribed = endpoints ∘ α
  decode-equivalence = decodeFun-isoMap-isEquiv (nameFun f) (nameFun g)
  chosen = equiv-lift decode-equivalence prescribed

  abstract
    endpoint-computation : prescribed =₂ ((decode-nameFun g) ⁻¹ ∙ (α ∙ decode-nameFun f))
    endpoint-computation =
      isoComp-cong (const-One ((decode-nameFun g) ⁻¹))
        (isoComp-cong (idIso α) (const-One (decode-nameFun f))) ∙
      (left-evaluate ((decode-nameFun g) ⁻¹) (α ∙ const (decode-nameFun f)) ∙
        ((leftMultiply ((decode-nameFun g) ⁻¹) ◁ right-evaluate (decode-nameFun f) α) ∙
          comp-assoc α (rightMultiply (decode-nameFun f)) (leftMultiply ((decode-nameFun g) ⁻¹))))

    image : decodeFunIso (nameFunIso α) =₂ ((decode-nameFun g) ⁻¹ ∙ (α ∙ decode-nameFun f))
    image = endpoint-computation ∙
      (FunctorLift.comparison chosen ∙
        (decodeFun-isoMap (nameFun f) (nameFun g) ◁
          comp-assoc α endpoints (IsEquiv.inverse decode-equivalence)))
```
