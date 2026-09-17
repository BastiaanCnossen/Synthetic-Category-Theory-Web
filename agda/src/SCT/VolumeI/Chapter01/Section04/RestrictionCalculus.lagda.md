# Equivalences for pairs of restriction maps

This file collects the endpoint transports used by the coproduct
isomorphism-anima restriction theorem. Every transport is an actual
equivalence of animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.Whiskering as W
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.FamilyNaturality as FN

module SCT.VolumeI.Chapter01.Section04.RestrictionCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
open W vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; left-evaluate; right-evaluate)
open Parameterized vocabulary terminal products productLaws composition vertical
  using (assoc; right-cancel; right-cancelʳ)
open FN vocabulary terminal products productLaws composition vertical whiskering
  using (family-substitution-square-projection)

change-map-evaluate : {A C D : CAT} {f f′ g g′ : MAP C D}
  (p : =₁ f f′) (q : =₁ g g′) (u : MAP A (f ＝ g)) →
  =₁ (changeEndpoints-map p q ∘ u) (const q ∙ (u ∙ const (invIso p)))
change-map-evaluate p q u = isoComp-cong (idIso (const q)) (right-evaluate (invIso p) u) ∙
  (left-evaluate q (rightMultiply (invIso p) ∘ u) ∙
    comp-assoc u (rightMultiply (invIso p)) (leftMultiply q))

family-square-to-map : {A C D : CAT} {f f′ g g′ : MAP C D}
  (p : =₁ f f′) (q : =₁ g g′) (u : MAP A (f ＝ g)) (v : MAP A (f′ ＝ g′)) →
  =₁ (const q ∙ u) (v ∙ const p) → =₁ (changeEndpoints-map p q ∘ u) v
family-square-to-map p q u v κ = right-cancel p v ∙
  (isoComp-cong κ (idIso (const (invIso p))) ∙
  (invIso (assoc (const q) u (const (invIso p))) ∙ change-map-evaluate p q u))

change-map-square : {A C D : CAT} {f f′ g g′ : MAP C D}
  (p : =₁ f f′) (q : =₁ g g′) (u : MAP A (f ＝ g)) →
  =₁ (const q ∙ u) ((changeEndpoints-map p q ∘ u) ∙ const p)
change-map-square p q u = isoComp-cong (invIso (change-map-evaluate p q u)) (idIso (const p)) ∙
  (invIso (assoc (const q) (u ∙ const (invIso p)) (const p)) ∙
    isoComp-cong (idIso (const q)) (invIso (right-cancelʳ p u)))

pair-after : {A B C D E : CAT} (f : MAP B D) (g : MAP C E) (u : MAP A B) (v : MAP A C) →
  =₁ (productMap f g ∘ pair u v) (pair (f ∘ u) (g ∘ v))
pair-after f g u v = pair-cong
  ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
  ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g) ∙
    pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v)

productMap-isEquiv : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′) →
  IsEquiv f → IsEquiv g → IsEquiv (productMap f g)
productMap-isEquiv {C} {C′} {D} {D′} f g ef eg = record
  { inverse = productMap (IsEquiv.inverse ef) (IsEquiv.inverse eg)
  ; sectionIso = invIso (productMap-comp f (IsEquiv.inverse ef) g (IsEquiv.inverse eg)) ∙
      (productMap-cong (IsEquiv.sectionIso ef) (IsEquiv.sectionIso eg) ∙ invIso (productMap-id C D))
  ; retractionIso = invIso (productMap-comp (IsEquiv.inverse ef) f (IsEquiv.inverse eg) g) ∙
      (productMap-cong (IsEquiv.retractionIso ef) (IsEquiv.retractionIso eg) ∙ invIso (productMap-id C′ D′)) }

pair-after-isEquiv : {A B C D E : CAT} (f : MAP B D) (g : MAP C E) (u : MAP A B) (v : MAP A C) →
  IsEquiv f → IsEquiv g → IsEquiv (pair u v) → IsEquiv (pair (f ∘ u) (g ∘ v))
pair-after-isEquiv f g u v ef eg e = equiv-transport (pair-after f g u v)
  (equiv-compose (pair u v) (productMap f g) e (productMap-isEquiv f g ef eg))

pair-squares-isEquiv : {A C D C′ D′ : CAT}
  {f₁ f₁′ g₁ g₁′ : MAP C D} {f₂ f₂′ g₂ g₂′ : MAP C′ D′}
  (p₁ : =₁ f₁ f₁′) (q₁ : =₁ g₁ g₁′) (p₂ : =₁ f₂ f₂′) (q₂ : =₁ g₂ g₂′)
  (u₁ : MAP A (f₁ ＝ g₁)) (u₂ : MAP A (f₂ ＝ g₂))
  (v₁ : MAP A (f₁′ ＝ g₁′)) (v₂ : MAP A (f₂′ ＝ g₂′)) →
  =₁ (const q₁ ∙ u₁) (v₁ ∙ const p₁) → =₁ (const q₂ ∙ u₂) (v₂ ∙ const p₂) →
  IsEquiv (pair u₁ u₂) → IsEquiv (pair v₁ v₂)
pair-squares-isEquiv p₁ q₁ p₂ q₂ u₁ u₂ v₁ v₂ κ₁ κ₂ e = equiv-transport
  (pair-cong (family-square-to-map p₁ q₁ u₁ v₁ κ₁) (family-square-to-map p₂ q₂ u₂ v₂ κ₂))
  (pair-after-isEquiv (changeEndpoints-map p₁ q₁) (changeEndpoints-map p₂ q₂) u₁ u₂
    (changeEndpoints-map-isEquiv p₁ q₁) (changeEndpoints-map-isEquiv p₂ q₂) e)

paired-post-isEquiv : {X Y Z T : CAT} (F : MAP X Y) (G : MAP X Z) →
  IsEquiv (pair F G) → (u v : MAP T X) → IsEquiv (pair (postWhisker {f = u} {v} F) (postWhisker G))
paired-post-isEquiv F G e u v = pair-squares-isEquiv bu bv cu cv
  (postWhisker pr₁ ∘ postWhisker H) (postWhisker pr₂ ∘ postWhisker H)
  (postWhisker F) (postWhisker G) leftSquare rightSquare
  (equiv-transport (pair-pre (postWhisker pr₁) (postWhisker pr₂) (postWhisker H))
    (equiv-compose (postWhisker H) (product-isoMap (H ∘ u) (H ∘ v))
      (postWhisker-isEquiv H e u v) (product-isoMap-isEquiv (H ∘ u) (H ∘ v))))
  where
  H = pair F G
  bu = (pair-β₁ F G ▷ u) ∙ invIso (comp-assoc u H pr₁)
  bv = (pair-β₁ F G ▷ v) ∙ invIso (comp-assoc v H pr₁)
  cu = (pair-β₂ F G ▷ u) ∙ invIso (comp-assoc u H pr₂)
  cv = (pair-β₂ F G ▷ v) ∙ invIso (comp-assoc v H pr₂)
  leftSquare = isoComp-cong (comp-unitʳ (postWhisker F)) (idIso (const bu)) ∙
    (family-substitution-square-projection pr₁ H F (pair-β₁ F G) (id (u ＝ v)) ∙
      isoComp-cong (idIso (const bv)) (postWhisker pr₁ ◁ invIso (comp-unitʳ (postWhisker H))))
  rightSquare = isoComp-cong (comp-unitʳ (postWhisker G)) (idIso (const cu)) ∙
    (family-substitution-square-projection pr₂ H G (pair-β₂ F G) (id (u ＝ v)) ∙
      isoComp-cong (idIso (const cv)) (postWhisker pr₂ ◁ invIso (comp-unitʳ (postWhisker H))))
```
