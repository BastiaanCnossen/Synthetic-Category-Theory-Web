# Decoding and precomposition

Decoding a point after precomposition agrees naturally with precomposing
the decoded functor. Both the source and target comparisons are actual
functors on their isomorphism animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FP
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.FamilyNaturality as FN

module SCT.VolumeI.Chapter01.Section03.DecodingNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open import SCT.VolumeI.Chapter01.Section03.Currying 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Points 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Functoriality 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.PrecompositionNaturality 𝒯 M
open FP vocabulary terminal products productLaws composition vertical whiskering using (paste-family-squares)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering using (preWhisker-comp-general)
open FN vocabulary terminal products productLaws composition vertical whiskering
  using (pre-const; pre-composition; family-interchange-fixedInner; family-move-square)

pre-family-square : {A R X C : CAT} {f f′ g g′ : MAP X C}
  (r : MAP R X) (b : =₁ f g) (b′ : =₁ f′ g′)
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′)) →
  =₁ (const b′ ∙ α) (β ∙ const b) →
  =₁ (const (b′ ▷ r) ∙ (α ▷ r)) ((β ▷ r) ∙ const (b ▷ r))
pre-family-square r b b′ α β p = isoComp-cong (idIso (β ▷ r)) (pre-const b r) ∙
  (pre-composition β (const b) r ∙
  ((preWhisker r ◁ p) ∙
  (invIso (pre-composition (const b′) α r) ∙
    isoComp-cong (invIso (pre-const b′ r)) (idIso (α ▷ r)))))

oneProduct-natural : {B C : CAT} (i : MAP B C) →
  =₁ (productMap (id One) i ∘ oneProduct-in B) (oneProduct-in C ∘ i)
oneProduct-natural {B} {C} i = pair-iso (terminal-iso _ _)
  (invIso (comp-unitˡ i ∙ project-pair₂ (terminate C) (id C) i) ∙
    (comp-unitʳ i ∙ ((i ◁ oneProduct-retraction B) ∙
    (comp-assoc (oneProduct-in B) pr₂ i ∙
      project-pair₂ (id One ∘ pr₁) (i ∘ pr₂) (oneProduct-in B)))))

decodeFamily : {A C D : CAT} {u v : Obj-abs (Map C D)} → MAP A (u ＝ v) → MAP A (decodeMap u ＝ decodeMap v)
decodeFamily {C = C} γ = uncurryFamily γ ▷ oneProduct-in C

decodeFamily-at : {A C D : CAT} {u v : Obj-abs (Map C D)} (γ : MAP A (u ＝ v)) →
  =₁ (decodeMap-isoMap u v ∘ γ) (decodeFamily γ)
decodeFamily-at {C = C} {u = u} {v} γ = (preWhisker (oneProduct-in C) ◁ uncurryFamily-at γ) ∙
  comp-assoc γ (mapUncurry-isoMap u v) (preWhisker (oneProduct-in C))

decodePre : {B C D : CAT} (i : MAP B C) (u : Obj-abs (Map C D)) →
  =₁ (decodeMap (mapPre i ∘ u)) (decodeMap u ∘ i)
decodePre {B} {C} i u = invIso (comp-assoc i (oneProduct-in C) (mapUncurry u)) ∙
  ((mapUncurry u ◁ oneProduct-natural i) ∙
  (comp-assoc (oneProduct-in B) (productMap (id One) i) (mapUncurry u) ∙
    (mapPre-uncurry i u ▷ oneProduct-in B)))

decodePre-family : {A B C D : CAT} (i : MAP B C)
  {u v : Obj-abs (Map C D)} (γ : MAP A (u ＝ v)) →
  =₁ (const (decodePre i v) ∙ decodeFamily (mapPre i ◁ γ))
    ((decodeFamily γ ▷ i) ∙ const (decodePre i u))
decodePre-family {B = B} {C} i {u} {v} γ =
  paste-family-squares (r₃u ∙ (r₂u ∙ r₁u)) (r₃v ∙ (r₂v ∙ r₁v)) r₄u r₄v action₀ action₃ action₄
    (paste-family-squares (r₂u ∙ r₁u) (r₂v ∙ r₁v) r₃u r₃v action₀ action₂ action₃
      (paste-family-squares r₁u r₁v r₂u r₂v action₀ action₁ action₂
        (pre-family-square (oneProduct-in B) (mapPre-uncurry i u) (mapPre-uncurry i v)
          (uncurryFamily (mapPre i ◁ γ)) (uncurryFamily γ ▷ R) (mapPre-uncurry-inputs i γ))
        (preWhisker-comp-general (uncurryFamily γ) R (oneProduct-in B)))
      (invIso (family-interchange-fixedInner (uncurryFamily γ) (oneProduct-natural i))))
    (family-move-square (comp-assoc i (oneProduct-in C) (mapUncurry v)) action₄ action₃
      (comp-assoc i (oneProduct-in C) (mapUncurry u))
      (preWhisker-comp-general (uncurryFamily γ) (oneProduct-in C) i))
  where
  R = productMap (id One) i
  r₁u = mapPre-uncurry i u ▷ oneProduct-in B
  r₁v = mapPre-uncurry i v ▷ oneProduct-in B
  r₂u = comp-assoc (oneProduct-in B) R (mapUncurry u)
  r₂v = comp-assoc (oneProduct-in B) R (mapUncurry v)
  r₃u = mapUncurry u ◁ oneProduct-natural i
  r₃v = mapUncurry v ◁ oneProduct-natural i
  r₄u = invIso (comp-assoc i (oneProduct-in C) (mapUncurry u))
  r₄v = invIso (comp-assoc i (oneProduct-in C) (mapUncurry v))
  action₀ = decodeFamily (mapPre i ◁ γ)
  action₁ = (uncurryFamily γ ▷ R) ▷ oneProduct-in B
  action₂ = uncurryFamily γ ▷ (R ∘ oneProduct-in B)
  action₃ = uncurryFamily γ ▷ (oneProduct-in C ∘ i)
  action₄ = decodeFamily γ ▷ i

decodePre-natural : {A B C D : CAT} (i : MAP B C)
  {u v : Obj-abs (Map C D)} (γ : MAP A (u ＝ v)) →
  =₁ (const (decodePre i v) ∙ (decodeMap-isoMap _ _ ∘ (mapPre i ◁ γ)))
    (((decodeMap-isoMap u v ∘ γ) ▷ i) ∙ const (decodePre i u))
decodePre-natural i {u} {v} γ =
  isoComp-cong (preWhisker i ◁ invIso (decodeFamily-at γ)) (idIso (const (decodePre i u))) ∙
    (decodePre-family i γ ∙ isoComp-cong (idIso (const (decodePre i v))) (decodeFamily-at (mapPre i ◁ γ)))
```
