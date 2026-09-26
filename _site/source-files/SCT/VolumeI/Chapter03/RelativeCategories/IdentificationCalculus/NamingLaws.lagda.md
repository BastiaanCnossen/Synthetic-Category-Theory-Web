# Naming composition and postcomposition of identifications

The laws for the chosen naming operation follow by reflection through
decoding. The proof uses the prescribed image of each named identification
and the normalization of the postcomposition comparison, rather than
assuming naturality of an arbitrary lifted comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.PostNamingCoherence as PostNaming

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingLaws
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ using (post-nameFun; decodeFun-post)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingCoherence 𝒯 M ℱ
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

abstract
  nameFunIso-square : {C D : CAT} {f g : MAP C D} (α : f =₁ g) →
    (decode-nameFun g ∙ decodeFunIso (nameFunIso α)) =₂ (α ∙ decode-nameFun f)
  nameFunIso-square {f = f} {g} α = cancel-inverse (decode-nameFun g) (α ∙ decode-nameFun f) ∙
    isoComp-cong (idIso (decode-nameFun g)) (NamedIdentification.image f g α)

  nameFunIso-comp : {C D : CAT} {f g h : MAP C D} (β : g =₁ h) (α : f =₁ g) →
    nameFunIso (β ∙ α) =₂ (nameFunIso β ∙ nameFunIso α)
  nameFunIso-comp {f = f} {g} {h} β α = equiv-reflect
    (decodeFun-isoMap-isEquiv (nameFun f) (nameFun h)) _ _
    (cancel-left-reflect (decode-nameFun h)
      ((isoComp-cong (idIso (decode-nameFun h)) (decodeFunIso-comp (nameFunIso β) (nameFunIso α))) ⁻¹ ∙
        (paste-iso-squares (decodeFunIso (nameFunIso α)) α (decodeFunIso (nameFunIso β)) β
          (decode-nameFun f) (decode-nameFun g) (decode-nameFun h)
          ((nameFunIso-square α) ⁻¹) ((nameFunIso-square β) ⁻¹) ∙ nameFunIso-square (β ∙ α))))

module Post {B C D : CAT} (g : MAP C D) {h k : MAP B C} (α : h =₁ k) where
  δh : decodeFun (nameFun h) =₁ h
  δh = decode-nameFun h
  δk : decodeFun (nameFun k) =₁ k
  δk = decode-nameFun k
  δgh : decodeFun (nameFun (g ∘ h)) =₁ (g ∘ h)
  δgh = decode-nameFun (g ∘ h)
  δgk : decodeFun (nameFun (g ∘ k)) =₁ (g ∘ k)
  δgk = decode-nameFun (g ∘ k)
  Nh : (funPost g ∘ nameFun h) =₁ nameFun (g ∘ h)
  Nh = post-nameFun g h
  Nk : (funPost g ∘ nameFun k) =₁ nameFun (g ∘ k)
  Nk = post-nameFun g k
  named : nameFun h =₁ nameFun k
  named = nameFunIso α
  dh : decodeFun (funPost g ∘ nameFun h) =₁ (g ∘ decodeFun (nameFun h))
  dh = decodeFun-post g (nameFun h)
  dk : decodeFun (funPost g ∘ nameFun k) =₁ (g ∘ decodeFun (nameFun k))
  dk = decodeFun-post g (nameFun k)
  left : (funPost g ∘ nameFun h) =₁ nameFun (g ∘ k)
  left = Nk ∙ (funPost g ◁ named)
  right : (funPost g ∘ nameFun h) =₁ nameFun (g ∘ k)
  right = nameFunIso (g ◁ α) ∙ Nh

  abstract
    left-normal : (δgk ∙ decodeFunIso left) =₂ ((g ◁ α) ∙ ((g ◁ δh) ∙ dh))
    left-normal = isoComp-assoc-at (g ◁ α) (g ◁ δh) dh ∙
      (isoComp-cong (postWhisker-isoComp-at g α δh ∙ (postWhisker g ◁ nameFunIso-square α)) (idIso dh) ∙
        (isoComp-cong ((postWhisker-isoComp-at g δk (decodeFunIso named)) ⁻¹) (idIso dh) ∙
          ((isoComp-assoc-at (g ◁ δk) (g ◁ decodeFunIso named) dh) ⁻¹ ∙
            (isoComp-cong (idIso (g ◁ δk)) (DecodePost.natural g named) ∙
              (isoComp-assoc-at (g ◁ δk) dk (decodeFunIso (funPost g ◁ named)) ∙
                (isoComp-cong (PostNaming.Normalization.comparison 𝒯 M ℱ g k)
                  (idIso (decodeFunIso (funPost g ◁ named))) ∙
                  ((isoComp-assoc-at δgk (decodeFunIso Nk) (decodeFunIso (funPost g ◁ named))) ⁻¹ ∙
                    isoComp-cong (idIso δgk) (decodeFunIso-comp Nk (funPost g ◁ named)))))))))

    right-normal : (δgk ∙ decodeFunIso right) =₂ ((g ◁ α) ∙ ((g ◁ δh) ∙ dh))
    right-normal = isoComp-cong (idIso (g ◁ α)) (PostNaming.Normalization.comparison 𝒯 M ℱ g h) ∙
      (isoComp-assoc-at (g ◁ α) δgh (decodeFunIso Nh) ∙
        (isoComp-cong (nameFunIso-square (g ◁ α)) (idIso (decodeFunIso Nh)) ∙
          ((isoComp-assoc-at δgk (decodeFunIso (nameFunIso (g ◁ α))) (decodeFunIso Nh)) ⁻¹ ∙
            isoComp-cong (idIso δgk) (decodeFunIso-comp (nameFunIso (g ◁ α)) Nh))))

    natural : left =₂ right
    natural = equiv-reflect
      (decodeFun-isoMap-isEquiv (funPost g ∘ nameFun h) (nameFun (g ∘ k))) left right
      (cancel-left-reflect δgk ((right-normal) ⁻¹ ∙ left-normal))
```
