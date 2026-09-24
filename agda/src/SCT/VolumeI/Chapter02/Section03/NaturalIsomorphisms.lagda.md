# Identifications of functors and natural isomorphisms

For `cor:Identifications_And_Natural_Isomorphisms`, first identify the
identification anima of two functors with that of their names in the
functor category. Uncurrying and the terminal-product equivalence give
this comparison. Applying the preceding fiber theorem then gives the
category of invertible natural transformations with the specified ends.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.Representability as Representability
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter02.Section03.NaturalIsomorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (Rep : Representability.Representability 𝒯 P) where

open import SCT.VolumeI.Chapter02.Section03.RezkFibers 𝒯 M ℱ P I E R Rep public
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M
  using (oneProduct-in; oneProduct-in-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
  using (funUncurry-isoMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯
  using (changeEndpoints-map; changeEndpoints-map-isEquiv)

decodeFun-isoMap : {C D : CAT} (u v : Obj-abs (Fun C D)) →
  MAP (u ＝ v) (decodeFun u ＝ decodeFun v)
decodeFun-isoMap {C} u v = preWhisker (oneProduct-in C) ∘ funUncurry-isoMap u v

decodeFun-isoMap-isEquiv : {C D : CAT} (u v : Obj-abs (Fun C D)) →
  IsEquiv (decodeFun-isoMap u v)
decodeFun-isoMap-isEquiv {C} u v = equiv-compose
  (funUncurry-isoMap u v) (preWhisker (oneProduct-in C))
  (funUncurry-isoMap-isEquiv u v)
  (preWhisker-isEquiv (oneProduct-in C) (oneProduct-in-isEquiv C)
    (funUncurry u) (funUncurry v))

nameFun-isoMap : {C D : CAT} (f g : MAP C D) →
  MAP (f ＝ g) (nameFun f ＝ nameFun g)
nameFun-isoMap f g =
  IsEquiv.inverse (decodeFun-isoMap-isEquiv (nameFun f) (nameFun g)) ∘
    changeEndpoints-map ((decode-nameFun f) ⁻¹) ((decode-nameFun g) ⁻¹)

nameFun-isoMap-isEquiv : {C D : CAT} (f g : MAP C D) →
  IsEquiv (nameFun-isoMap f g)
nameFun-isoMap-isEquiv f g = equiv-compose
  (changeEndpoints-map ((decode-nameFun f) ⁻¹) ((decode-nameFun g) ⁻¹))
  (IsEquiv.inverse (decodeFun-isoMap-isEquiv (nameFun f) (nameFun g)))
  (changeEndpoints-map-isEquiv ((decode-nameFun f) ⁻¹) ((decode-nameFun g) ⁻¹))
  (equiv-inverse (decodeFun-isoMap-isEquiv (nameFun f) (nameFun g)))

NatIsoBetween : {C D : CAT} → MAP C D → MAP C D → CAT
NatIsoBetween f g = IsoBetween (nameFun f) (nameFun g)

module NaturalIdentification {C D : CAT} (f g : MAP C D) where
  private
    module Fiber = IdentificationFiber (nameFun f) (nameFun g)

  identification-to-natural-iso : MAP (f ＝ g) (NatIsoBetween f g)
  identification-to-natural-iso = Fiber.identification-to-iso ∘ nameFun-isoMap f g

  identification-to-natural-iso-isEquiv : IsEquiv identification-to-natural-iso
  identification-to-natural-iso-isEquiv = equiv-compose
    (nameFun-isoMap f g) Fiber.identification-to-iso
    (nameFun-isoMap-isEquiv f g) Fiber.identification-to-iso-isEquiv
```
