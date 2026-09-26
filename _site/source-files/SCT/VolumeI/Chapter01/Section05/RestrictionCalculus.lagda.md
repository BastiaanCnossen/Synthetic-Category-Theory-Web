# Equivalences for pairs of restriction maps

This file collects the endpoint transports used by the coproduct
isomorphism-anima restriction theorem. Every transport is an actual
equivalence of animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.Whiskering as W
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FamilyNaturality as FN

module SCT.VolumeI.Chapter01.Section05.RestrictionCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
open W vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; left-evaluate; right-evaluate)
open Parameterized vocabulary terminal products productLaws composition vertical
  using (assoc; right-cancel; right-cancelʳ)
open FN vocabulary terminal products productLaws composition vertical whiskering
  using (family-substitution-square-projection)

change-map-evaluate : {A C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (u : MAP A (f ＝ g)) →
  (changeEndpoints-map p q ∘ u) =₁ (const q ∙ (u ∙ const (p ⁻¹)))
change-map-evaluate p q u = isoComp-cong (idIso (const q)) (right-evaluate (p ⁻¹) u) ∙
  (left-evaluate q (rightMultiply (p ⁻¹) ∘ u) ∙
    comp-assoc u (rightMultiply (p ⁻¹)) (leftMultiply q))

family-square-to-map : {A C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (u : MAP A (f ＝ g)) (v : MAP A (f′ ＝ g′)) →
  (const q ∙ u) =₁ (v ∙ const p) → (changeEndpoints-map p q ∘ u) =₁ v
family-square-to-map p q u v κ = right-cancel p v ∙
  (isoComp-cong κ (idIso (const (p ⁻¹))) ∙
  ((assoc (const q) u (const (p ⁻¹))) ⁻¹ ∙ change-map-evaluate p q u))

change-map-square : {A C D : CAT} {f f′ g g′ : MAP C D}
  (p : f =₁ f′) (q : g =₁ g′) (u : MAP A (f ＝ g)) →
  (const q ∙ u) =₁ ((changeEndpoints-map p q ∘ u) ∙ const p)
change-map-square p q u = isoComp-cong ((change-map-evaluate p q u) ⁻¹) (idIso (const p)) ∙
  ((assoc (const q) (u ∙ const (p ⁻¹)) (const p)) ⁻¹ ∙
    isoComp-cong (idIso (const q)) ((right-cancelʳ p u) ⁻¹))

pair-after : {A B C D E : CAT} (f : MAP B D) (g : MAP C E) (u : MAP A B) (v : MAP A C) →
  (productMap f g ∘ pair u v) =₁ (pair (f ∘ u) (g ∘ v))
pair-after f g u v = pair-cong
  ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
  ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g) ∙
    pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v)

productMap-isEquiv : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′) →
  IsEquiv f → IsEquiv g → IsEquiv (productMap f g)
productMap-isEquiv {C} {C′} {D} {D′} f g ef eg = record
  { inverse = productMap (IsEquiv.inverse ef) (IsEquiv.inverse eg)
  ; sectionIso = (productMap-comp f (IsEquiv.inverse ef) g (IsEquiv.inverse eg)) ⁻¹ ∙
      (productMap-cong (IsEquiv.sectionIso ef) (IsEquiv.sectionIso eg) ∙ (productMap-id C D) ⁻¹)
  ; retractionIso = (productMap-comp (IsEquiv.inverse ef) f (IsEquiv.inverse eg) g) ⁻¹ ∙
      (productMap-cong (IsEquiv.retractionIso ef) (IsEquiv.retractionIso eg) ∙ (productMap-id C′ D′) ⁻¹) }

pair-after-isEquiv : {A B C D E : CAT} (f : MAP B D) (g : MAP C E) (u : MAP A B) (v : MAP A C) →
  IsEquiv f → IsEquiv g → IsEquiv (pair u v) → IsEquiv (pair (f ∘ u) (g ∘ v))
pair-after-isEquiv f g u v ef eg e = equiv-transport (pair-after f g u v)
  (equiv-compose (pair u v) (productMap f g) e (productMap-isEquiv f g ef eg))

pair-squares-isEquiv : {A C D C′ D′ : CAT}
  {f₁ f₁′ g₁ g₁′ : MAP C D} {f₂ f₂′ g₂ g₂′ : MAP C′ D′}
  (p₁ : f₁ =₁ f₁′) (q₁ : g₁ =₁ g₁′) (p₂ : f₂ =₁ f₂′) (q₂ : g₂ =₁ g₂′)
  (u₁ : MAP A (f₁ ＝ g₁)) (u₂ : MAP A (f₂ ＝ g₂))
  (v₁ : MAP A (f₁′ ＝ g₁′)) (v₂ : MAP A (f₂′ ＝ g₂′)) →
  (const q₁ ∙ u₁) =₁ (v₁ ∙ const p₁) → (const q₂ ∙ u₂) =₁ (v₂ ∙ const p₂) →
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
  bu = (pair-β₁ F G ▷ u) ∙ (comp-assoc u H pr₁) ⁻¹
  bv = (pair-β₁ F G ▷ v) ∙ (comp-assoc v H pr₁) ⁻¹
  cu = (pair-β₂ F G ▷ u) ∙ (comp-assoc u H pr₂) ⁻¹
  cv = (pair-β₂ F G ▷ v) ∙ (comp-assoc v H pr₂) ⁻¹
  leftSquare = isoComp-cong (comp-unitʳ (postWhisker F)) (idIso (const bu)) ∙
    (family-substitution-square-projection pr₁ H F (pair-β₁ F G) (id (u ＝ v)) ∙
      isoComp-cong (idIso (const bv)) (postWhisker pr₁ ◁ (comp-unitʳ (postWhisker H)) ⁻¹))
  rightSquare = isoComp-cong (comp-unitʳ (postWhisker G)) (idIso (const cu)) ∙
    (family-substitution-square-projection pr₂ H G (pair-β₂ F G) (id (u ＝ v)) ∙
      isoComp-cong (idIso (const cv)) (postWhisker pr₂ ◁ (comp-unitʳ (postWhisker H)) ⁻¹))
```
